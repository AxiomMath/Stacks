module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismPropertiesSupplement
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties

/-!
# Descent of properties of a morphism to an affine base, with no bound on the index

Let `B` be a big fppf site over a scheme `S`, let `D : I ⥤ BigAffineFppf B S hS` be a diagram of
*affine* objects of the site indexed by a cofiltered category `I`, and let `c` be a cone over `D`
whose cone of underlying schemes is a limit. Write `T_j` for the representable presheaf
`yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj j))` and `T` for the one attached to the
vertex of `c`. Let `i` be a stage and let `z : Z ⟶ T_i` be a quasi-compact algebraic space over
`T_i`. Base changing `z` along `yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map g))` for
`g : j ⟶ i`, respectively along the leg of the cone at `i`, gives algebraic spaces `Z_j` over
`T_j` and `Z_T` over `T`.

This file proves that flatness and a bound on the relative dimension descend from `Z_T ⟶ T` to
`Z_j ⟶ T_j` for some `g : j ⟶ i`, with **no cardinality hypothesis on `I`** and no
`AlgebraicGeometry.Space.ChartsBounded` hypothesis.

The two statements are the affine-base forms of the last sentence of Stacks 08K0 and of
Stacks 0D4K. Both tags are already registered, in the bounded
`AlgebraicGeometry.Space.MorphismDescentSystemOfChartsBounded` form, on
`AlgebraicGeometry.Space.MorphismDescentSystemOfChartsBounded.exists_isFlat_mapAt` and
`AlgebraicGeometry.Space.MorphismDescentSystemOfChartsBounded.exists_hasRelativeDimensionLE_mapAt`;
the declarations here are a different, incomparable reading of the same two tags (the base system
is a system of affine objects of the site rather than a system of algebraic spaces, but the index
category is unrestricted), so they carry no `@[stacks]` attribute of their own.

## Main results

* `AlgebraicGeometry.Space.exists_isFlat_baseChange_of_isFlat_limit`: the affine-base, size-free
  form of the final sentence of **Stacks 08K0**.
* `AlgebraicGeometry.Space.exists_hasRelativeDimensionLE_baseChange_of_limit`: the affine-base,
  size-free form of **Stacks 0D4K**.

## Implementation notes

The index bound of the bounded results pays for the construction of a limit of charts *inside* the
site. Here that construction is unnecessary: the base is a system of affine objects whose limit is
given at the level of schemes, so the system of charts of the base is the system `D` itself and the
chart of each stage is the identity. What remains is purely the chart reduction of the property,
and the scheme-level descent results it ends at
(`AlgebraicGeometry.exists_flat_baseChange_of_limitBaseChange`, Stacks 04AI, and
`AlgebraicGeometry.exists_fiberDimensionLE_baseChange_of_limitBaseChange`, the scheme-level content
of Stacks 0D4K) carry no cardinality hypothesis: they ask only for `EssentiallySmall.{u} I`, which
`CategoryTheory.essentiallySmallSelf` supplies for `I : Type u` with `Category.{u} I`.

Because the target of the morphism being descended is representable at every stage, a square of
étale charts of `Z_j ⟶ T_j` is obtained from one étale chart `a` of `Z` alone, with the identity of
`T_j` as the chart of the target; `Z` is assumed quasi-compact so that `a` may be taken with affine
source, which is what the scheme-level results consume.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 04AI](https://stacks.math.columbia.edu/tag/04AI)
* [Stacks Project, Tag 08K0](https://stacks.math.columbia.edu/tag/08K0)
* [Stacks Project, Tag 0D4K](https://stacks.math.columbia.edu/tag/0D4K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

/-- Pullbacks of presheaves on the big fppf site over `S`, given directly: instance search for
them times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_AffineBasePropertyDescent
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  CategoryTheory.Limits.functorCategoryHasLimitsOfShape

/-- The pullback of two morphisms of presheaves on the big fppf site over `S`. -/
local instance (priority := high) hasPullback_presheaf_AffineBasePropertyDescent
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

section AffineBaseCharts

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

variable {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Ti Tj Vs : BigFppfOver B S hS}

/-- A property of morphisms of schemes which holds on every square of étale charts of the base
change of the structure morphism `z` along `yoneda.map m` holds for the morphism of schemes
underlying the base changed chart morphism. -/
private theorem prop_chartMap_of_holdsOnEveryEtaleChart_affineBase
    (P : MorphismProperty Scheme.{u}) (z : Z ⟶ yoneda.obj Ti) (a : yoneda.obj Vs ⟶ Z)
    (qa : Vs ⟶ Ti) (hqa : yoneda.map qa = a ≫ z) (ha : relEtale B S hS a) (m : Tj ⟶ Ti)
    (hevery : HoldsOnEveryEtaleChart B S hS P (pullback.fst (yoneda.map m) z)) :
    P ((BigFppfOver.toScheme B S hS).map (pullback.snd qa m)) := by
  have hmul := isMultiplicative_presheaf_etale B S hS
  exact hevery _ Tj (baseChangedChart z a qa hqa m) (𝟙 _) (pullback.snd qa m)
    (MorphismProperty.of_isPullback (isPullback_baseChangedChart z a qa hqa m) ha)
    (MorphismProperty.id_mem _ _)
    (by rw [Category.comp_id, baseChangedChart_comp_fst])

/-- Conversely, if the base changed chart morphism has the property and the chart `a` is in
addition surjective, then the property holds on a surjective square of étale charts of the base
change of `z` along `yoneda.map m`. -/
private theorem holdsOnSurjectiveEtaleChart_of_prop_chartMap_affineBase
    (P : MorphismProperty Scheme.{u}) (z : Z ⟶ yoneda.obj Ti) (a : yoneda.obj Vs ⟶ Z)
    (qa : Vs ⟶ Ti) (hqa : yoneda.map qa = a ≫ z) (ha : relEtale B S hS a)
    (hs : relSurjective B S hS a) (m : Tj ⟶ Ti)
    (hP : P ((BigFppfOver.toScheme B S hS).map (pullback.snd qa m))) :
    HoldsOnSurjectiveEtaleChart B S hS P (pullback.fst (yoneda.map m) z) := by
  have hmul := isMultiplicative_presheaf_etale B S hS
  refine ⟨pullback qa m, Tj, baseChangedChart z a qa hqa m, 𝟙 _, pullback.snd qa m,
    MorphismProperty.of_isPullback (isPullback_baseChangedChart z a qa hqa m) ha,
    MorphismProperty.id_mem _ _,
    MorphismProperty.of_isPullback (isPullback_baseChangedChart z a qa hqa m) hs, ?_, hP⟩
  rw [Category.comp_id, baseChangedChart_comp_fst]

/-- The morphism of schemes underlying the base changed chart morphism, read as the base change
in `Over` of the chart morphism viewed as an object over the representable base. -/
private theorem prop_chartMap_iff_overPullback (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (qa : Vs ⟶ Ti) (m : Tj ⟶ Ti) :
    P ((BigFppfOver.toScheme B S hS).map (pullback.snd qa m)) ↔
      P ((Over.pullback ((BigFppfOver.toScheme B S hS).map m)).map
        (Over.homMk ((BigFppfOver.toScheme B S hS).map qa) :
          Over.mk ((BigFppfOver.toScheme B S hS).map qa) ⟶
            Over.mk (𝟙 ((BigFppfOver.toScheme B S hS).obj Ti)))).left :=
  ((CategoryTheory.prop_snd_iff_of_isPullback P
        ((IsPullback.of_hasPullback qa m).map (BigFppfOver.toScheme B S hS))
        (IsPullback.of_hasPullback _ _)).trans
    (CategoryTheory.prop_overPullback_map_left_iff_pullback_snd P
      ((BigFppfOver.toScheme B S hS).map qa) ((BigFppfOver.toScheme B S hS).map m)).symm)


/-- The every-chart condition transported along an isomorphism of the source. -/
private theorem holdsOnEveryEtaleChart_of_iso (P : MorphismProperty Scheme.{u})
    {X X' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : X ≅ X') {f : X ⟶ Y} {f' : X' ⟶ Y}
    (h : e.inv ≫ f = f') (hf : HoldsOnEveryEtaleChart B S hS P f) :
    HoldsOnEveryEtaleChart B S hS P f' := by
  have : (relEtale B S hS).RespectsIso := MorphismProperty.relative_respectsIso _
  intro U V a b hh haE hbE hcomm
  refine hf U V (a ≫ e.inv) b hh
    (((relEtale B S hS).cancel_right_of_respectsIso a e.inv).2 haE) hbE ?_
  rw [Category.assoc, h]
  exact hcomm

/-- The every-chart condition passes from the source of a cartesian square to the canonical fibre
product. -/
private theorem holdsOnEveryEtaleChart_fst_of_isPullback (P : MorphismProperty Scheme.{u})
    {X Y W Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {fT : X ⟶ W} {gT : X ⟶ Y} {m : W ⟶ Q}
    {fi : Y ⟶ Q} (hsq : IsPullback fT gT m fi) (hf : HoldsOnEveryEtaleChart B S hS P fT) :
    HoldsOnEveryEtaleChart B S hS P (pullback.fst m fi) :=
  holdsOnEveryEtaleChart_of_iso P hsq.isoPullback
    (by rw [Iso.inv_comp_eq]; exact hsq.isoPullback_hom_fst.symm) hf

/-- The scheme-level descent statement for morphisms of affine schemes over a stage, from the same
statement with the finiteness hypotheses of the scheme-level results available as instances. -/
private theorem exists_baseChange_of_affine_system {I : Type u} [Category.{u} I]
    (D : I ⥤ BigAffineFppf B S hS) {c : Cone D} (i : I) (R P : MorphismProperty Scheme.{u})
    (key : ∀ (X₀ Y₀ : Over ((D ⋙ BigAffineFppf.toScheme B S hS).obj i)) (f₀ : X₀ ⟶ Y₀)
      [∀ {j k : I} (g : j ⟶ k),
        _root_.AlgebraicGeometry.IsAffineHom ((D ⋙ BigAffineFppf.toScheme B S hS).map g)]
      [IsAffine ((D ⋙ BigAffineFppf.toScheme B S hS).obj i)]
      [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
      [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left], R f₀.left →
      P ((Over.pullback (((BigAffineFppf.toScheme B S hS).mapCone c).π.app i)).map f₀).left →
      ∃ (j : I) (g : j ⟶ i),
        P ((Over.pullback ((D ⋙ BigAffineFppf.toScheme B S hS).map g)).map f₀).left) :
    ∀ (X₀ Y₀ : Over ((D ⋙ BigAffineFppf.toScheme B S hS).obj i)) (f₀ : X₀ ⟶ Y₀),
      IsAffine X₀.left → IsAffine Y₀.left → R f₀.left →
      P ((Over.pullback (((BigAffineFppf.toScheme B S hS).mapCone c).π.app i)).map f₀).left →
      ∃ (j : I) (g : j ⟶ i),
        P ((Over.pullback ((D ⋙ BigAffineFppf.toScheme B S hS).map g)).map f₀).left := by
  intro X₀ Y₀ f₀ hX hY hR hP
  have hEaff : ∀ j : I, IsAffine ((D ⋙ BigAffineFppf.toScheme B S hS).obj j) := fun j ↦
    BigAffineFppf.isAffine_toScheme_obj B S hS (D.obj j)
  have : ∀ {j k : I} (g : j ⟶ k),
      _root_.AlgebraicGeometry.IsAffineHom ((D ⋙ BigAffineFppf.toScheme B S hS).map g) := by
    intro j k g
    have := hEaff j
    have := hEaff k
    exact _root_.AlgebraicGeometry.isAffineHom_of_isAffine _
  have := hEaff i
  have : CompactSpace X₀.left := Scheme.compactSpace_of_isAffine _
  have : CompactSpace Y₀.left := Scheme.compactSpace_of_isAffine _
  exact key X₀ Y₀ f₀ hR hP

end AffineBaseCharts

/-! ### Descending a property along a cofiltered system of affine objects of the site -/

section AffineBaseDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ BigAffineFppf B S hS) {c : Cone D}

omit [IsCofiltered I] in
/-- The shared argument behind the two descent statements below. The base being a system of
affine objects of the site, a square of étale charts of the base change of the structure
morphism `z` is obtained from one affine étale surjective chart of `Z` alone, with the identity
of the representable base as the chart of the target; so a property of morphisms of algebraic
spaces that is read off such a square reduces to the property `P` of a morphism of affine
schemes over the stage, and the descent of `P` along the system of schemes is the input
`hdescend`. -/
private theorem exists_holdsOnSurjectiveEtaleChart_of_holdsOnEveryEtaleChart_limit
    (i : I)
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso] (R : MorphismProperty Scheme.{u})
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (z : Z ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))
    (hZ : IsAlgebraicSpace B S hS Z) (hqc : IsQuasiCompactSpace B S hS Z)
    (hR : HoldsOnEveryEtaleChart B S hS R z)
    (hdescend : ∀ (X₀ Y₀ : Over ((D ⋙ BigAffineFppf.toScheme B S hS).obj i)) (f₀ : X₀ ⟶ Y₀),
      IsAffine X₀.left → IsAffine Y₀.left → R f₀.left →
      P ((Over.pullback (((BigAffineFppf.toScheme B S hS).mapCone c).π.app i)).map f₀).left →
      ∃ (j : I) (g : j ⟶ i),
        P ((Over.pullback ((D ⋙ BigAffineFppf.toScheme B S hS).map g)).map f₀).left)
    (hlimit : HoldsOnEveryEtaleChart B S hS P
      (pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) z)) :
    ∃ (j : I) (g : j ⟶ i), HoldsOnSurjectiveEtaleChart B S hS P
      (pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map g))) z) := by
  classical
  have hmul := isMultiplicative_presheaf_etale B S hS
  obtain ⟨Vs, a, hVsAff, haSurj, haEt⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Z hZ).mp hqc
  have ha : relEtale B S hS a := (isEtale_iff_presheaf_of_yoneda B S hS a).mp haEt
  obtain ⟨qa, hqa⟩ : ∃ qa : Vs ⟶ (BigAffineFppf.inclusion B S hS).obj (D.obj i),
      yoneda.map qa = a ≫ z := ⟨yoneda.preimage (a ≫ z), yoneda.map_preimage _⟩
  have hRChart : R ((BigFppfOver.toScheme B S hS).map qa) :=
    hR Vs _ a (𝟙 _) qa ha (MorphismProperty.id_mem _ _) (by rw [Category.comp_id, hqa])
  have hEaff : ∀ j : I, IsAffine ((D ⋙ BigAffineFppf.toScheme B S hS).obj j) := fun j ↦
    BigAffineFppf.isAffine_toScheme_obj B S hS (D.obj j)
  obtain ⟨j, g, hg⟩ := hdescend (Over.mk ((BigFppfOver.toScheme B S hS).map qa)) (Over.mk (𝟙 _))
    (Over.homMk ((BigFppfOver.toScheme B S hS).map qa)) hVsAff (hEaff i) hRChart
    ((prop_chartMap_iff_overPullback _ qa ((BigAffineFppf.inclusion B S hS).map (c.π.app i))).mp
      (prop_chartMap_of_holdsOnEveryEtaleChart_affineBase _ z a qa hqa ha _ hlimit))
  exact ⟨j, g, holdsOnSurjectiveEtaleChart_of_prop_chartMap_affineBase _ z a qa hqa ha haSurj _
    ((prop_chartMap_iff_overPullback _ qa
      ((BigAffineFppf.inclusion B S hS).map (D.map g))).mpr hg)⟩

/-! #### Flatness -/

/-- **The affine-base, size-free form of the final sentence of Stacks 08K0.** Let `D` be a
cofiltered inverse system of affine objects of the big fppf site over `S` whose cone `c` has a
limiting cone of underlying schemes, let `i` be a stage, and let `z : Z ⟶ T_i` be a quasi-compact
algebraic space over the representable presheaf `T_i` attached to `D.obj i`, with `z` locally of
finite presentation. If the base change of `z` along the leg of `c` at `i` is flat, then its base
change along `D.map g` is flat for some `g : j ⟶ i`.

There is no cardinality hypothesis on `I` and no `AlgebraicGeometry.Space.ChartsBounded`
hypothesis: the system of étale charts of the base is `D` itself, so the scheme-level descent
Stacks 04AI applies to it directly. -/
theorem exists_isFlat_baseChange_of_isFlat_limit
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) (i : I)
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (z : Z ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))
    (hZ : IsAlgebraicSpace B S hS Z) (hqc : IsQuasiCompactSpace B S hS Z)
    (hfp : IsLocallyOfFinitePresentation B S hS z)
    (hflat : IsFlat B S hS
      (pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) z)) :
    ∃ (j : I) (g : j ⟶ i), IsFlat B S hS
      (pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map g))) z) := by
  have : EssentiallySmall.{u} I := inferInstance
  have hriF : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hdescend := exists_baseChange_of_affine_system D (c := c) i
    (@LocallyOfFinitePresentation) (@_root_.AlgebraicGeometry.Flat.{u})
    fun X₀ Y₀ f₀ _ _ _ _ _ _ hfp' hlim' ↦
      AlgebraicGeometry.exists_flat_baseChange_of_limitBaseChange
      (D ⋙ BigAffineFppf.toScheme B S hS) ((BigAffineFppf.toScheme B S hS).mapCone c) i
      X₀ Y₀ f₀ hc
  obtain ⟨j, g, hj⟩ := exists_holdsOnSurjectiveEtaleChart_of_holdsOnEveryEtaleChart_limit
    B S hS D i (@_root_.AlgebraicGeometry.Flat.{u}) (@LocallyOfFinitePresentation) z hZ hqc
    hfp hdescend hflat
  refine ⟨j, g, (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS _
    _root_.AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget
    (isAlgebraicSpace_pullback B S hS _ z (isAlgebraicSpace_yoneda B S hS _) hZ
      (isAlgebraicSpace_yoneda B S hS _))
    (isAlgebraicSpace_yoneda B S hS _) _).mpr hj⟩

/-- **The affine-base, size-free form of the final sentence of Stacks 08K0, stated over an
arbitrary cartesian square.** The base change of `fi` to the vertex of the cone is presented by
any cartesian square over the cone leg rather than by the canonical fibre product, and the
conclusion produces the stage, the morphism `s : k ⟶ i` of the index category, and a cartesian
square over `D.map s`. -/
theorem exists_isFlat_isPullback_of_isFlat_limit
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) (i : I)
    {Zi : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (fi : Zi ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))
    (hZi : IsAlgebraicSpace B S hS Zi) (hqc : IsQuasiCompactSpace B S hS Zi)
    (hfp : IsLocallyOfFinitePresentation B S hS fi)
    {ZT : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (fT : ZT ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj c.pt)) (gT : ZT ⟶ Zi)
    (hsq : IsPullback fT gT
      (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) fi)
    (hflat : IsFlat B S hS fT) :
    ∃ (k : I) (s : k ⟶ i) (Zk : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (fk : Zk ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj k)))
      (hk : Zk ⟶ Zi),
      IsPullback fk hk
          (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map s))) fi ∧
        IsFlat B S hS fk := by
  obtain ⟨k, s, h⟩ := exists_isFlat_baseChange_of_isFlat_limit B S hS D hc i fi hZi hqc hfp
    (holdsOnEveryEtaleChart_fst_of_isPullback _ hsq hflat)
  exact ⟨k, s, _, _, _, IsPullback.of_hasPullback _ _, h⟩

/-! #### Relative dimension -/

/-- The relative-dimension descent with its hypothesis at the limit phrased on the squares of
étale charts, which is the form the two public statements below share. -/
private theorem exists_hasRelativeDimensionLE_baseChange_of_holdsOnEveryEtaleChart_limit
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) (i : I) (d : ℕ)
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (z : Z ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))
    (hZ : IsAlgebraicSpace B S hS Z) (hqc : IsQuasiCompactSpace B S hS Z)
    (hft : IsLocallyOfFiniteType B S hS z)
    (hdim : HoldsOnEveryEtaleChart B S hS (AlgebraicGeometry.fiberDimensionLE d)
      (pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) z)) :
    ∃ (j : I) (g : j ⟶ i), HasRelativeDimensionLE d B S hS
      (pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map g))) z) := by
  have : EssentiallySmall.{u} I := inferInstance
  have hdescend := exists_baseChange_of_affine_system D (c := c) i
    (@LocallyOfFiniteType) (AlgebraicGeometry.fiberDimensionLE d)
    fun X₀ Y₀ f₀ _ _ _ _ _ _ hft' hlim' ↦
      AlgebraicGeometry.exists_fiberDimensionLE_baseChange_of_limitBaseChange
      (D ⋙ BigAffineFppf.toScheme B S hS) hc i X₀ Y₀ f₀ d hlim'
  obtain ⟨j, g, hj⟩ := exists_holdsOnSurjectiveEtaleChart_of_holdsOnEveryEtaleChart_limit
    B S hS D i (AlgebraicGeometry.fiberDimensionLE d) (@LocallyOfFiniteType) z hZ hqc hft
    hdescend hdim
  exact ⟨j, g, hasRelativeDimensionLE_of_holdsOnSurjectiveEtaleChart B S hS
    (isAlgebraicSpace_pullback B S hS _ z (isAlgebraicSpace_yoneda B S hS _) hZ
      (isAlgebraicSpace_yoneda B S hS _)) _ d hj⟩

/-- **The affine-base, size-free form of Stacks 0D4K.** Let `D` be a cofiltered inverse system of
affine objects of the big fppf site over `S` whose cone `c` has a limiting cone of underlying
schemes, let `i` be a stage, and let `z : Z ⟶ T_i` be a quasi-compact algebraic space over the
representable presheaf `T_i` attached to `D.obj i`, with `z` locally of finite type. If the base
change of `z` along the leg of `c` at `i` has relative dimension at most `d`, then its base change
along `D.map g` has relative dimension at most `d` for some `g : j ⟶ i`.

There is no cardinality hypothesis on `I` and no `AlgebraicGeometry.Space.ChartsBounded`
hypothesis. -/
theorem exists_hasRelativeDimensionLE_baseChange_of_limit
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) (i : I) (d : ℕ)
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (z : Z ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))
    (hZ : IsAlgebraicSpace B S hS Z) (hqc : IsQuasiCompactSpace B S hS Z)
    (hft : IsLocallyOfFiniteType B S hS z)
    (hdim : HasRelativeDimensionLE d B S hS
      (pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) z)) :
    ∃ (j : I) (g : j ⟶ i), HasRelativeDimensionLE d B S hS
      (pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map g))) z) :=
  exists_hasRelativeDimensionLE_baseChange_of_holdsOnEveryEtaleChart_limit B S hS D hc i d z hZ
    hqc hft (fiberDimensionLE_chartMap_of_hasRelativeDimensionLE B S hS _ d hdim)

/-- **The affine-base, size-free form of Stacks 0D4K, stated over an arbitrary cartesian
square.** The base change of `fi` to the vertex of the cone is presented by any cartesian square
over the cone leg rather than by the canonical fibre product, and the conclusion produces the
stage, the morphism `s : k ⟶ i` of the index category, and a cartesian square over `D.map s`. -/
theorem exists_hasRelativeDimensionLE_isPullback_of_limit
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) (i : I) (d : ℕ)
    {Zi : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (fi : Zi ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))
    (hZi : IsAlgebraicSpace B S hS Zi) (hqc : IsQuasiCompactSpace B S hS Zi)
    (hft : IsLocallyOfFiniteType B S hS fi)
    {ZT : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (fT : ZT ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj c.pt)) (gT : ZT ⟶ Zi)
    (hsq : IsPullback fT gT
      (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) fi)
    (hdim : HasRelativeDimensionLE d B S hS fT) :
    ∃ (k : I) (s : k ⟶ i) (Zk : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (fk : Zk ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj k)))
      (hk : Zk ⟶ Zi),
      IsPullback fk hk
          (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map s))) fi ∧
        HasRelativeDimensionLE d B S hS fk := by
  obtain ⟨k, s, h⟩ := exists_hasRelativeDimensionLE_baseChange_of_holdsOnEveryEtaleChart_limit
    B S hS D hc i d fi hZi hqc hft
    (holdsOnEveryEtaleChart_fst_of_isPullback _ hsq
      (fiberDimensionLE_chartMap_of_hasRelativeDimensionLE B S hS fT d hdim))
  exact ⟨k, s, _, _, _, IsPullback.of_hasPullback _ _, h⟩

end AffineBaseDescent

end AlgebraicGeometry.Space

end
