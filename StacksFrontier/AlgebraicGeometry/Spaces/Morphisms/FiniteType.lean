module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints

/-!
# Morphisms of algebraic spaces locally of finite type

An immersion of algebraic spaces over a scheme `S` is locally of finite type, and local finite
type of a morphism of algebraic spaces over `S` can be tested in nine equivalent ways: at the
points of the source, after base change to a scheme or to an affine scheme, on a single étale
chart of the source or of the target, on all commuting squares of étale charts, on one such
square with surjective chart of the source, or on Zariski coverings.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isImmersion`: **Stacks 06ED**, an
  immersion of algebraic spaces over `S` is locally of finite type.
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_tfae`: **Stacks 040Y**, the nine equivalent
  local criteria for a morphism of algebraic spaces over `S` to be locally of finite type.

The implications of Stacks 040Y are proved separately and are useful on their own:

* `AlgebraicGeometry.Space.isFiniteTypeAt_of_isLocallyOfFiniteType` and
  `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isFiniteTypeAt` are (1) ⇔ (2).
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_pullback_fst'`,
  `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_pullback_fst` and
  `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_pullback_fst_of_isAffine` are (1) ⇔ (3)
  and (4) ⇒ (1).
* `AlgebraicGeometry.Space.exists_targetAtlas_isLocallyOfFiniteType`,
  `AlgebraicGeometry.Space.exists_sourceAtlas_isLocallyOfFiniteType`,
  `AlgebraicGeometry.Space.holdsOnSurjectiveEtaleChart_of_targetAtlas` and
  `AlgebraicGeometry.Space.holdsOnSurjectiveEtaleChart_of_sourceAtlas` are (1) ⇒ (5), (1) ⇒
  (6), (5) ⇒ (8) and (6) ⇒ (8).
* `AlgebraicGeometry.Space.exists_zariskiCover_isLocallyOfFiniteType` and
  `AlgebraicGeometry.Space.isFiniteTypeAt_of_zariskiCover` are (1) ⇒ (9) and (9) ⇒ (2).

## Implementation notes

An immersion of algebraic spaces, Stacks 02YU part (5), is a representable morphism all of
whose represented base changes are immersions of schemes; being locally of finite type,
Stacks 03XF part (1), is instead stated on the commuting squares of étale charts. The two
readings are bridged by the implication of Stacks 03MJ in the form
`AlgebraicGeometry.Space.presheafImpliesHoldsOnEveryEtaleChart_locallyOfFiniteType`, so all
that is left is that an immersion of schemes is locally of finite type, which Mathlib has as
an instance of `AlgebraicGeometry.IsImmersion`. This is the same route as the one taken for a
closed immersion by
`AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isClosedImmersion` of
`StacksFrontier/AlgebraicGeometry/Spaces/ProperClosedImmersion.lean`, and the statement here
subsumes it, a closed immersion being an immersion. Neither its statement nor its proof uses
the algebraic-space conditions on source and target, so it is given for an arbitrary morphism
of presheaves on the big fppf site of `S`.

Conditions (1) and (7) of Stacks 040Y are the *same* statement in this development: local
finite type of Stacks 03XF part (1) is by definition the every-étale-chart condition of Stacks
03MJ at Mathlib's `AlgebraicGeometry.LocallyOfFiniteType`. The equivalence of (7) with (8) is
therefore Stacks 03MJ itself,
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_surjectiveChart`, applied to a property
which is étale local on the source and target by Stacks 04R3.

The remaining implications divide into three groups. The base-change criteria (3) and (4) are
compared with the charts by factoring a chart square of `f` through the base change of `f`
along the chart of the target: the comparison morphism is étale over the source chart, by
Stacks 03FV, so it is itself an étale chart. For (3) that base change is available directly;
for (4) only affine test objects are allowed, so an arbitrary chart square is first refined
over the affine open covering of its target chart, which is legitimate because being locally
of finite type is Zariski local at the target. The two atlas criteria (5) and (6) are compared
with condition (8) by composing a chart square with the atlas, using that surjectivity and
étaleness are stable under composition and, for (5), under base change along the atlas (Stacks
03FU, 03MH).

The pointwise criterion (2) and the Zariski criterion (9) are compared through the open
subspaces of Stacks 02YU part (2). From (1) both follow with the *whole* space as the only
open subspace and the trivial Zariski covering of Stacks 02YY. Conversely, (2) gives local
finite type because being locally of finite type is étale local on the source and target in
the neighbourhood form of Stacks 04R3: around a point of a chart `U` of the source, the
inverse image in `U` of the open neighbourhood supplied by (2) is an open subspace of `U` by
Stacks 083Q and 02YW, and any chart of it is the required étale neighbourhood. And (9) gives
(2) because a point of the source lies in some member of the inner covering of the inverse
image of some member of the outer covering, and the image of that member in the source — the
range subfunctor of the composite of the two inclusions — is an open neighbourhood of the
point over which `f` is locally of finite type.

## References

* [Stacks Project, Tag 040Y](https://stacks.math.columbia.edu/tag/040Y)
* [Stacks Project, Tag 06ED](https://stacks.math.columbia.edu/tag/06ED)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Pullbacks of presheaves on the big fppf site (instance search for `HasLimit (cospan f g)`
times out without this shortcut). -/
local instance (priority := high) hasLimit_cospan_presheaf_FiniteType
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- A morphism of the big fppf site of `S` whose underlying morphism of schemes is an
immersion is locally of finite type, Mathlib's `AlgebraicGeometry.IsImmersion` being an
instance of `AlgebraicGeometry.LocallyOfFiniteType`. -/
theorem inverseImage_isImmersion_le_inverseImage_locallyOfFiniteType :
    MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS) ≤
      MorphismProperty.inverseImage
        (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS) := by
  intro U V h hh
  have : _root_.AlgebraicGeometry.IsImmersion
    ((BigFppfOver.toScheme B S hS).map h) := hh
  exact inferInstanceAs (LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map h))

/-- **Stacks 06ED.** An immersion of algebraic spaces over `S` is locally of finite type.
Each of its represented base changes is an immersion of schemes, hence locally of finite
type, and being locally of finite type passes from the represented base changes to the étale
charts by the implication of Stacks 03MJ. -/
@[stacks 06ED]
theorem isLocallyOfFiniteType_of_isImmersion (f : X ⟶ Y) (hf : IsImmersion B S hS f) :
    IsLocallyOfFiniteType B S hS f :=
  presheafImpliesHoldsOnEveryEtaleChart_locallyOfFiniteType B S hS f
    (MorphismProperty.relative_monotone
      (inverseImage_isImmersion_le_inverseImage_locallyOfFiniteType B S hS) _ hf)


/-! ### Glue: points, open subspaces and squares of algebraic spaces -/

/-- A Cartesian square of presheaves whose four corners are algebraic spaces over `S` is
Cartesian in the category of algebraic spaces over `S`. -/
theorem isPullback_homMk
    {F G H K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H) (hK : IsAlgebraicSpace B S hS K)
    {p : K ⟶ F} {q : K ⟶ G} {f : F ⟶ H} {g : G ⟶ H} (sq : IsPullback p q f g) :
    IsPullback
      (ObjectProperty.homMk p : (⟨K, hK⟩ : AlgebraicSpaces B S hS) ⟶ ⟨F, hF⟩)
      (ObjectProperty.homMk q : (⟨K, hK⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩)
      (ObjectProperty.homMk f : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨H, hH⟩)
      (ObjectProperty.homMk g : (⟨G, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨H, hH⟩) :=
  IsPullback.of_map_of_faithful (F := ObjectProperty.ι _) sq

/-- The inclusion of an open subspace is étale and locally of finite type. -/
private theorem isLocallyOfFiniteType_ι_of_isOpenSubspace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {Z : Subfunctor X} (hZ : IsOpenSubspace B S hS Z) :
    IsLocallyOfFiniteType B S hS Z.ι :=
  isLocallyOfFiniteType_of_isEtale B S hS hX (isEtale_ι_of_isOpenSubspace hZ)

/-! ### The implications of Stacks 040Y -/

/-- **Stacks 040Y, (1) implies (2).** A morphism of algebraic spaces over `S` which is locally
of finite type is of finite type at every point of its source: the whole source is an open
neighbourhood of every point. -/
theorem isFiniteTypeAt_of_isLocallyOfFiniteType (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f) (x : points B S hS X) :
    IsFiniteTypeAt B S hS f x := by
  have hTop : IsOpenSubspace B S hS (⊤ : Subfunctor X) := isOpenSubspace_top hX
  obtain ⟨x', hx'⟩ := pointsMap_surjective_of_isIso B S hS (⊤ : Subfunctor X).ι x
  exact ⟨⊤, hTop, x', hx', isLocallyOfFiniteType_comp B S hS hTop.1 hX hY (⊤ : Subfunctor X).ι f
    (isLocallyOfFiniteType_ι_of_isOpenSubspace B S hS hX hTop) hf⟩

/-- **Stacks 040Y, (1) implies (3).** Being locally of finite type is inherited by the base
change along an arbitrary morphism from a scheme over `S`; this is Stacks 03XH.

The base is an arbitrary algebraic space over `S` rather than a scheme over `S`, which is what
distinguishes this from `AlgebraicGeometry.Space.isLocallyOfFiniteType_pullback_fst`: that form
is condition (3) of Stacks 040Y as stated there, tests the base change along a morphism out of a
representable presheaf, and is the special case of this one at `Z = yoneda.obj V`. -/
theorem isLocallyOfFiniteType_pullback_fst' (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Z ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f) :
    IsLocallyOfFiniteType B S hS (pullback.fst g f) :=
  (isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS
      (ObjectProperty.homMk g : (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
      (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)).flip hf

/-- A commuting square of étale charts of `f` factors through the base change of `f` along the
chart of the target, by a morphism that is étale over the source chart (Stacks 03FV). -/
private theorem exists_presheaf_etale_lift_pullback (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) {U V : BigFppfOver B S hS}
    (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (α : U ⟶ V)
    (ha : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hsquare : yoneda.map α ≫ b = a ≫ f) :
    ∃ k : yoneda.obj U ⟶ Limits.pullback b f,
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf k ∧ k ≫ pullback.fst b f = yoneda.map α := by
  have hValg := isAlgebraicSpace_yoneda B S hS V
  have hpb := AlgebraicSpaces.isPullback_fiberProduct B S hS
    (ObjectProperty.homMk b : (⟨yoneda.obj V, hValg⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
    (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
  refine ⟨pullback.lift (yoneda.map α) a hsquare, ?_, pullback.lift_fst _ _ _⟩
  exact presheaf_etale_of_isEtale B S hS
    (isEtale_of_isEtale_over B S hS (isAlgebraicSpace_yoneda B S hS U)
      (isAlgebraicSpace_pullback B S hS b f hValg hX hY) hX _ a (pullback.snd b f)
      (isEtale_of_presheaf_etale B S hS ha)
      (isEtale_of_isPullback B S hS _ _ _ _ hpb (isEtale_of_presheaf_etale B S hS hb))
      (pullback.lift_snd _ _ _))

/-- **Stacks 040Y, (3) implies (1).** It is enough to test the base changes along the
morphisms from schemes over `S`: an étale chart square of `f` is an étale chart square of the
base change along the chart of the target. -/
theorem isLocallyOfFiniteType_of_pullback_fst (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (h3 : ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
      IsLocallyOfFiniteType B S hS (pullback.fst g f)) :
    IsLocallyOfFiniteType B S hS f := by
  intro U V a b h ha hb hsquare
  obtain ⟨k, hk, hkfst⟩ := exists_presheaf_etale_lift_pullback B S hS hX hY f a b h ha hb hsquare
  refine h3 V b U V k (𝟙 (yoneda.obj V)) h hk (presheaf_etale_id B S hS V) ?_
  rw [Category.comp_id, hkfst]


/-- **Stacks 040Y, (4) implies (1)** on an étale chart square with *affine* target chart: the
chart square factors through the base change of `f` along the target chart. -/
private theorem locallyOfFiniteType_map_of_isAffine (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (h4 : ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
        IsLocallyOfFiniteType B S hS (pullback.fst g f))
    (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (α : U ⟶ V)
    (ha : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hsquare : yoneda.map α ≫ b = a ≫ f)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) :
    LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map α) := by
  obtain ⟨k, hk, hkfst⟩ := exists_presheaf_etale_lift_pullback B S hS hX hY f a b α ha hb hsquare
  refine h4 V b hV U V k (𝟙 (yoneda.obj V)) α hk (presheaf_etale_id B S hS V) ?_
  rw [Category.comp_id, hkfst]

/-- **Stacks 040Y, (4) implies (1).** It is enough to test the base changes along the
morphisms from *affine* schemes over `S`: being locally of finite type is Zariski local at the
target, so an arbitrary étale chart square may be refined over an affine open covering of its
target chart, where the previous lemma applies. -/
theorem isLocallyOfFiniteType_of_pullback_fst_of_isAffine (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (h4 : ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
        IsLocallyOfFiniteType B S hS (pullback.fst g f)) :
    IsLocallyOfFiniteType B S hS f := by
  intro U V a b α ha hb hsquare
  set T := BigFppfOver.toScheme B S hS
  set C := (T.obj V).affineCover
  have _ : IsZariskiLocalAtTarget (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.FiniteType)
  apply MorphismProperty.IsLocalAtTarget.of_zeroHypercover
    (P := @LocallyOfFiniteType.{u}) C
  intro i
  have hVi : B.Contains (C.X i) :=
    lt_of_le_of_lt (Scheme.size_le_of_mono_locallyOfFinitePresentation (C.f i))
      V.left.property
  set j₀ : B.obj hVi ⟶ V.left :=
    B.inclusion.preimage (X := B.obj hVi) (Y := V.left) (C.f i) with hj₀def
  set Vi : BigFppfOver B S hS := Over.mk (j₀ ≫ V.hom)
  set j : Vi ⟶ V := Over.homMk j₀
  have hj : T.map j = C.f i := by
    change B.inclusion.map j₀ = C.f i
    rw [B.inclusion.map_preimage]
  have hViAffine : IsAffine (T.obj Vi) := by
    change IsAffine (C.X i)
    exact Scheme.isAffine_affineCover (T.obj V) i
  have hWsch : B.Contains (Limits.pullback (T.map α) (C.f i)) :=
    Scheme.size_pullback_lt _ _ U.left.property hVi
  set pU₀ : B.obj hWsch ⟶ U.left :=
    B.inclusion.preimage (X := B.obj hWsch) (Y := U.left)
      (pullback.fst (T.map α) (C.f i)) with hpU₀def
  set pV₀ : B.obj hWsch ⟶ B.obj hVi :=
    B.inclusion.preimage (X := B.obj hWsch) (Y := B.obj hVi)
      (pullback.snd (T.map α) (C.f i)) with hpV₀def
  set W : BigFppfOver B S hS := Over.mk (pU₀ ≫ U.hom)
  set pU : W ⟶ U := Over.homMk pU₀
  have hαbase : T.map α ≫ B.inclusion.map V.hom = B.inclusion.map U.hom := by
    change B.inclusion.map α.left ≫ B.inclusion.map V.hom = B.inclusion.map U.hom
    rw [← Functor.map_comp, α.w]
  have hOver : pV₀ ≫ Vi.hom = pU₀ ≫ U.hom := by
    apply B.inclusion.map_injective
    change B.inclusion.map pV₀ ≫ B.inclusion.map (j₀ ≫ V.hom) =
      B.inclusion.map pU₀ ≫ B.inclusion.map U.hom
    simp only [Functor.map_comp, hpV₀def, hpU₀def, hj₀def, B.inclusion.map_preimage]
    calc pullback.snd (T.map α) (C.f i) ≫ C.f i ≫ B.inclusion.map V.hom
        = (pullback.fst (T.map α) (C.f i) ≫ T.map α) ≫ B.inclusion.map V.hom := by
          rw [← Category.assoc, ← pullback.condition]
      _ = pullback.fst (T.map α) (C.f i) ≫ B.inclusion.map U.hom := by
          rw [Category.assoc, hαbase]
  set pV : W ⟶ Vi := Over.homMk pV₀ hOver
  have hleft : pV₀ ≫ j₀ = pU₀ ≫ α.left := by
    apply B.inclusion.map_injective
    simp only [Functor.map_comp, hpV₀def, hpU₀def, hj₀def, B.inclusion.map_preimage]
    exact (pullback.condition (f := T.map α) (g := C.f i)).symm
  have hpull : pV ≫ j = pU ≫ α := Over.OverMorphism.ext hleft
  have hcomm : yoneda.map pV ≫ (yoneda.map j ≫ b) = (yoneda.map pU ≫ a) ≫ f := by
    rw [← Category.assoc, ← yoneda.map_comp, hpull, yoneda.map_comp, Category.assoc,
      hsquare, Category.assoc]
  have _ : AlgebraicGeometry.IsOpenImmersion (C.f i) := C.map_prop i
  have hjOpen : AlgebraicGeometry.IsOpenImmersion (T.map j) := by rw [hj]; infer_instance
  have hpUeq : T.map pU = pullback.fst (T.map α) (C.f i) := by
    change B.inclusion.map pU₀ = pullback.fst (T.map α) (C.f i)
    rw [B.inclusion.map_preimage]
  have hpVeq : T.map pV = pullback.snd (T.map α) (C.f i) := by
    change B.inclusion.map pV₀ = pullback.snd (T.map α) (C.f i)
    rw [B.inclusion.map_preimage]
  have hpUOpen : AlgebraicGeometry.IsOpenImmersion (T.map pU) := by
    rw [hpUeq]; infer_instance
  have hQbc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T).IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS
      AlgebraicGeometry.Etale.etale_isStableUnderBaseChange
  have hjChart : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T).presheaf
      (yoneda.map j) :=
    (MorphismProperty.relative_map_iff (F := yoneda)
      (P := MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T)).2
      (show AlgebraicGeometry.Etale (T.map j) from by have := hjOpen; infer_instance)
  have hpUChart : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T).presheaf
      (yoneda.map pU) :=
    (MorphismProperty.relative_map_iff (F := yoneda)
      (P := MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T)).2
      (show AlgebraicGeometry.Etale (T.map pU) from by have := hpUOpen; infer_instance)
  have hmul := isMultiplicative_presheaf_etale B S hS
  have htop := locallyOfFiniteType_map_of_isAffine B S hS hX hY f h4 W Vi
    (yoneda.map pU ≫ a) (yoneda.map j ≫ b) pV
    (MorphismProperty.comp_mem _ _ _ hpUChart ha)
    (MorphismProperty.comp_mem _ _ _ hjChart hb) hcomm hViAffine
  rwa [hpVeq] at htop


/-- An isomorphism of presheaves on the big fppf site of `S` is locally of finite type. -/
private theorem isLocallyOfFiniteType_of_isIso
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hG : IsAlgebraicSpace B S hS G)
    (e : F ⟶ G) [IsIso e] : IsLocallyOfFiniteType B S hS e := by
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).ContainsIdentities :=
    ⟨fun U ↦ by
      change AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (𝟙 U))
      rw [CategoryTheory.Functor.map_id]
      infer_instance⟩
  have _ : MorphismProperty.RespectsIso (@AlgebraicGeometry.Etale.{u}) :=
    MorphismProperty.RespectsIso.mk _
      (fun e g hg ↦ by
        have _ : AlgebraicGeometry.Etale e.hom := inferInstance
        have _ : AlgebraicGeometry.Etale g := hg
        infer_instance)
      (fun e g hg ↦ by
        have _ : AlgebraicGeometry.Etale e.hom := inferInstance
        have _ : AlgebraicGeometry.Etale g := hg
        infer_instance)
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  exact isLocallyOfFiniteType_of_isEtale B S hS hG
    (isEtale_of_presheaf_etale B S hS (MorphismProperty.presheaf_of_isIso _ e))

/-- A point of the source of a morphism which maps into an open subspace of the target lies in
the image of the inverse image of that subspace: this is Stacks 03H4 for the Cartesian square
of Stacks 083Q. -/
private theorem mem_range_pointsMap_preimage
    {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : Y' ⟶ X') (Z : Subfunctor X')
    (hX' : IsAlgebraicSpace B S hS X') (hY' : IsAlgebraicSpace B S hS Y')
    (hZ : IsOpenSubspace B S hS Z)
    (x : points B S hS Y') (z : points B S hS Z.toFunctor)
    (h : pointsMap B S hS Z.toFunctor Z.ι z = pointsMap B S hS Y' a x) :
    x ∈ Set.range (pointsMap B S hS (Z.preimage a).toFunctor (Z.preimage a).ι) := by
  have hP := isOpenSubspace_preimage B S hS a Z hX' hY' hZ
  obtain ⟨w, -, hw⟩ := exists_point_of_isPullback B S hS
    (isPullback_homMk B S hS hZ.1 hY' hX' hP.1 (Subfunctor.isPullback_preimage a Z)) z x h
  exact ⟨w, hw⟩

/-- **Stacks 040Y, (2) implies (1).** A morphism of algebraic spaces over `S` which is of
finite type at every point of its source is locally of finite type: being locally of finite
type is étale local on the source and target (Stacks 04R3), so it suffices to produce, around
every point of a chart `U` of the source, an étale neighbourhood over which the chart morphism
is locally of finite type; the inverse image in `U` of an open neighbourhood supplied by the
hypothesis, together with a chart of it, is such a neighbourhood. -/
theorem isLocallyOfFiniteType_of_isFiniteTypeAt (hX : IsAlgebraicSpace B S hS X)
    (_hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (h2 : ∀ x : points B S hS X, IsFiniteTypeAt B S hS f x) :
    IsLocallyOfFiniteType B S hS f := by
  intro U V a b α ha hb hchart
  set T := BigFppfOver.toScheme B S hS
  refine (LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget.{u}
    |>.iff_forall_exists_etale_neighborhood (T.map α)).2 ?_
  intro xU
  have hUalg := isAlgebraicSpace_yoneda B S hS U
  set pc := (schemePointRepresentative B S hS U xU).class B S hS (yoneda.obj U)
  have hpcx : pointsToScheme B S hS U pc = xU := schemePointRepresentative_point B S hS U xU
  obtain ⟨W, hWopen, zW, hzW, hWlft⟩ := h2 (pointsMap B S hS (yoneda.obj U) a pc)
  have hPopen : IsOpenSubspace B S hS (W.preimage a) :=
    isOpenSubspace_preimage B S hS a W hX hUalg hWopen
  obtain ⟨zP, hzP⟩ := Set.mem_range.mp
    (mem_range_pointsMap_preimage B S hS a W hX hUalg hWopen pc zW hzW)
  obtain ⟨A, φ, hφSurj, hφEtale⟩ := hPopen.1.exists_atlas
  obtain ⟨zA, hzA⟩ := (presheafSurjective_iff_isSurjective_yoneda B S hS
    (W.preimage a).toFunctor hPopen.1 A φ).1 hφSurj zP
  set c : A ⟶ U := yoneda.preimage (φ ≫ (W.preimage a).ι)
  have hc : yoneda.map c = φ ≫ (W.preimage a).ι := yoneda.map_preimage _
  have hclass : pointsMap B S hS (yoneda.obj A) (yoneda.map c) zA = pc := by
    rw [hc, pointsMap_comp B S hS (yoneda.obj A) φ (W.preimage a).ι]
    simp only [Function.comp_apply, hzA]
    exact hzP
  have hxA : T.map c (pointsToScheme B S hS A zA) = xU := by
    rw [← pointsToScheme_pointsMap B S hS c zA, hclass, hpcx]
  have hφE : IsEtale B S hS φ := isEtale_of_presheaf_etale B S hS hφEtale
  have hcEtale : IsEtale B S hS (yoneda.map c) := by
    rw [hc]
    exact isEtale_comp B S hS hφE (isEtale_ι_of_isOpenSubspace hPopen)
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T).IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS
      AlgebraicGeometry.Etale.etale_isStableUnderBaseChange
  have hcScheme : AlgebraicGeometry.Etale (T.map c) :=
    (MorphismProperty.relative_map_iff (F := yoneda)
      (P := MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T)).1
      (presheaf_etale_of_isEtale B S hS hcEtale)
  have hdiag : yoneda.map (c ≫ α) ≫ b = (φ ≫ W.fromPreimage a) ≫ W.ι ≫ f := by
    rw [yoneda.map_comp, Category.assoc, hchart, hc, Category.assoc, ← Category.assoc _ a,
      ← Subfunctor.fromPreimage_ι W a]
    simp
  have hlocal : LocallyOfFiniteType (T.map (c ≫ α)) :=
    hWlft A V (φ ≫ W.fromPreimage a) b (c ≫ α)
      (presheaf_etale_of_isEtale B S hS (isEtale_comp B S hS hφE
        (isEtale_of_isPullback B S hS _ _ _ _
          (isPullback_homMk B S hS hUalg hWopen.1 hX hPopen.1
            (Subfunctor.isPullback_preimage a W).flip) (isEtale_of_presheaf_etale B S hS ha))))
      hb hdiag
  refine ⟨T.obj A, T.obj V, T.map c, 𝟙 (T.obj V), T.map (c ≫ α),
    pointsToScheme B S hS A zA, hcScheme, inferInstance, hxA, ?_, ?_⟩
  · simp [Functor.map_comp]
  · simpa [Functor.map_comp] using hlocal

/-- **Stacks 040Y, (1) implies (9).** A morphism of algebraic spaces over `S` which is locally
of finite type satisfies the Zariski criterion, with the one-member covering of the target by
itself and of the inverse image by itself. -/
theorem exists_zariskiCover_isLocallyOfFiniteType (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f) :
    ∃ (I : Type u) (Yᵢ : I → Subfunctor Y), IsZariskiCover B S hS I Yᵢ ∧
      ∀ i, ∃ (J : Type u) (Xᵢⱼ : J → Subfunctor ((Yᵢ i).preimage f).toFunctor),
        IsZariskiCover B S hS J Xᵢⱼ ∧
          ∀ j, IsLocallyOfFiniteType B S hS ((Xᵢⱼ j).ι ≫ (Yᵢ i).fromPreimage f) := by
  have hYtop : IsOpenSubspace B S hS (⊤ : Subfunctor Y) := isOpenSubspace_top hY
  have hPf : IsOpenSubspace B S hS ((⊤ : Subfunctor Y).preimage f) :=
    isOpenSubspace_preimage B S hS f ⊤ hY hX hYtop
  have h1 : IsLocallyOfFiniteType B S hS (((⊤ : Subfunctor Y).preimage f).ι ≫ f) :=
    isLocallyOfFiniteType_comp B S hS hPf.1 hX hY _ f
      (isLocallyOfFiniteType_ι_of_isOpenSubspace B S hS hX hPf) hf
  have h1' : IsLocallyOfFiniteType B S hS
      ((⊤ : Subfunctor Y).fromPreimage f ≫ (⊤ : Subfunctor Y).ι) := by
    rwa [Subfunctor.fromPreimage_ι]
  have hq : IsLocallyOfFiniteType B S hS ((⊤ : Subfunctor Y).fromPreimage f) :=
    isLocallyOfFiniteType_of_comp B S hS hPf.1 hYtop.1 hY _ _ h1'
  refine ⟨PUnit.{u + 1}, fun _ ↦ ⊤, isZariskiCover_top hY, fun _ ↦
    ⟨PUnit.{u + 1}, fun _ ↦ ⊤, isZariskiCover_top hPf.1, fun _ ↦ ?_⟩⟩
  exact isLocallyOfFiniteType_comp B S hS (isOpenSubspace_top hPf.1).1 hPf.1 hYtop.1 _ _
    (isLocallyOfFiniteType_ι_of_isOpenSubspace B S hS hPf.1 (isOpenSubspace_top hPf.1)) hq

/-- **Stacks 040Y, (9) implies (2).** A morphism of algebraic spaces over `S` satisfying the
Zariski criterion is of finite type at every point of its source: a point lies in some member
of the inner covering of the inverse image of some member of the outer covering, and the image
of that member in the source is an open neighbourhood over which the morphism is locally of
finite type. -/
theorem isFiniteTypeAt_of_zariskiCover (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (h9 : ∃ (I : Type u) (Yᵢ : I → Subfunctor Y), IsZariskiCover B S hS I Yᵢ ∧
      ∀ i, ∃ (J : Type u) (Xᵢⱼ : J → Subfunctor ((Yᵢ i).preimage f).toFunctor),
        IsZariskiCover B S hS J Xᵢⱼ ∧
          ∀ j, IsLocallyOfFiniteType B S hS ((Xᵢⱼ j).ι ≫ (Yᵢ i).fromPreimage f))
    (x : points B S hS X) : IsFiniteTypeAt B S hS f x := by
  classical
  obtain ⟨I, Yᵢ, hYcover, hYdata⟩ := h9
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  have hyUnion : pointsMap B S hS X f (p.class B S hS X) ∈
      ⋃ i, Set.range (pointsMap B S hS (Yᵢ i).toFunctor (Yᵢ i).ι) := by
    rw [(isZariskiCover_iff_iUnion_points B S hS Y hY I Yᵢ hYcover.1).mp hYcover]
    exact Set.mem_univ _
  obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp hyUnion
  obtain ⟨zY, hzY⟩ := Set.mem_range.mp hyi
  have hPopen : IsOpenSubspace B S hS ((Yᵢ i).preimage f) :=
    isOpenSubspace_preimage B S hS f (Yᵢ i) hY hX (hYcover.1 i)
  obtain ⟨zP, hzP⟩ := Set.mem_range.mp (mem_range_pointsMap_preimage B S hS f (Yᵢ i) hY hX
    (hYcover.1 i) (p.class B S hS X) zY hzY)
  obtain ⟨J, Xᵢⱼ, hXcover, hXdata⟩ := hYdata i
  have hzUnion : zP ∈ ⋃ j, Set.range
      (pointsMap B S hS (Xᵢⱼ j).toFunctor (Xᵢⱼ j).ι) := by
    rw [(isZariskiCover_iff_iUnion_points B S hS ((Yᵢ i).preimage f).toFunctor hPopen.1
      J Xᵢⱼ hXcover.1).mp hXcover]
    exact Set.mem_univ _
  obtain ⟨j, hzj⟩ := Set.mem_iUnion.mp hzUnion
  obtain ⟨zX, hzX⟩ := Set.mem_range.mp hzj
  set k : (Xᵢⱼ j).toFunctor ⟶ X := (Xᵢⱼ j).ι ≫ ((Yᵢ i).preimage f).ι with hkdef
  have _ : Mono k := mono_comp _ _
  have hkOpen : IsOpenImmersion B S hS k :=
    MorphismProperty.comp_mem _ _ _ (hXcover.1 j).2 hPopen.2
  set e : (Xᵢⱼ j).toFunctor ≅ (Subfunctor.range k).toFunctor := asIso (Subfunctor.toRange k)
  have heqHom : e.hom ≫ (Subfunctor.range k).ι = k := Subfunctor.toRange_ι k
  have heq : e.inv ≫ k = (Subfunctor.range k).ι := e.inv_comp_eq.2 heqHom.symm
  have hWalg : IsAlgebraicSpace B S hS (Subfunctor.range k).toFunctor :=
    (hXcover.1 j).1.of_iso e
  have hRI : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.RespectsIso :=
    MorphismProperty.relative_respectsIso _
  have hWopen : IsOpenSubspace B S hS (Subfunctor.range k) := by
    refine ⟨hWalg, ?_⟩
    rw [← heq]
    exact MorphismProperty.RespectsIso.precomp _ e.inv k hkOpen
  have hXjY : IsLocallyOfFiniteType B S hS
      ((Xᵢⱼ j).ι ≫ (Yᵢ i).fromPreimage f ≫ (Yᵢ i).ι) := by
    have hcomp := isLocallyOfFiniteType_comp B S hS (hXcover.1 j).1 (hYcover.1 i).1 hY
      ((Xᵢⱼ j).ι ≫ (Yᵢ i).fromPreimage f) (Yᵢ i).ι (hXdata j)
      (isLocallyOfFiniteType_ι_of_isOpenSubspace B S hS hY (hYcover.1 i))
    simpa [Category.assoc] using hcomp
  have hkLft : IsLocallyOfFiniteType B S hS (k ≫ f) := by
    rw [hkdef, Category.assoc, ← Subfunctor.fromPreimage_ι (Yᵢ i) f]
    simpa [Category.assoc] using hXjY
  have hWlft : IsLocallyOfFiniteType B S hS ((Subfunctor.range k).ι ≫ f) := by
    rw [← heq, Category.assoc]
    exact isLocallyOfFiniteType_comp B S hS hWalg (hXcover.1 j).1 hY e.inv (k ≫ f)
      (isLocallyOfFiniteType_of_isIso B S hS (hXcover.1 j).1 e.inv) hkLft
  refine ⟨Subfunctor.range k, hWopen,
    pointsMap B S hS (Xᵢⱼ j).toFunctor e.hom zX, ?_, hWlft⟩
  calc pointsMap B S hS (Subfunctor.range k).toFunctor (Subfunctor.range k).ι
        (pointsMap B S hS (Xᵢⱼ j).toFunctor e.hom zX)
      = pointsMap B S hS (Xᵢⱼ j).toFunctor (e.hom ≫ (Subfunctor.range k).ι) zX :=
        (congrFun (pointsMap_comp B S hS (Xᵢⱼ j).toFunctor e.hom
          (Subfunctor.range k).ι) zX).symm
    _ = pointsMap B S hS (Xᵢⱼ j).toFunctor
          ((Xᵢⱼ j).ι ≫ ((Yᵢ i).preimage f).ι) zX := by rw [heqHom]
    _ = pointsMap B S hS ((Yᵢ i).preimage f).toFunctor ((Yᵢ i).preimage f).ι
          (pointsMap B S hS (Xᵢⱼ j).toFunctor (Xᵢⱼ j).ι zX) :=
        congrFun (pointsMap_comp B S hS (Xᵢⱼ j).toFunctor (Xᵢⱼ j).ι
          ((Yᵢ i).preimage f).ι) zX
    _ = pointsMap B S hS ((Yᵢ i).preimage f).toFunctor ((Yᵢ i).preimage f).ι zP := by
        rw [hzX]
    _ = p.class B S hS X := hzP


/-- **Stacks 040Y, (1) implies (5).** A morphism of algebraic spaces over `S` which is locally
of finite type stays so after base change along a surjective étale chart of its target. -/
theorem exists_targetAtlas_isLocallyOfFiniteType (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f) :
    ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y), IsSurjective B S hS g ∧
      IsEtale B S hS g ∧ IsLocallyOfFiniteType B S hS (pullback.fst g f) := by
  obtain ⟨V, g, hgSurj, hgEtale⟩ := hY.exists_atlas
  exact ⟨V, g, (presheafSurjective_iff_isSurjective_yoneda B S hS Y hY V g).1 hgSurj,
    isEtale_of_presheaf_etale B S hS hgEtale,
    isLocallyOfFiniteType_pullback_fst' B S hS hX hY
      (isAlgebraicSpace_yoneda B S hS V) f g hf⟩

/-- **Stacks 040Y, (1) implies (6).** A morphism of algebraic spaces over `S` which is locally
of finite type remains so after precomposition with a surjective étale chart of its source. -/
theorem exists_sourceAtlas_isLocallyOfFiniteType (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f) :
    ∃ (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ X), IsSurjective B S hS g ∧
      IsEtale B S hS g ∧ IsLocallyOfFiniteType B S hS (g ≫ f) := by
  obtain ⟨U, g, hgSurj, hgEtale⟩ := hX.exists_atlas
  have hgE : IsEtale B S hS g := isEtale_of_presheaf_etale B S hS hgEtale
  exact ⟨U, g, (presheafSurjective_iff_isSurjective_yoneda B S hS X hX U g).1 hgSurj, hgE,
    isLocallyOfFiniteType_comp B S hS (isAlgebraicSpace_yoneda B S hS U) hX hY g f
      (isLocallyOfFiniteType_of_isEtale B S hS hX hgE) hf⟩

/-- The composite of two morphisms of presheaves that are surjective on points is surjective. -/
private theorem isSurjective_comp_aux {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} {g : G ⟶ H} (hf : IsSurjective B S hS f) (hg : IsSurjective B S hS g) :
    IsSurjective B S hS (f ≫ g) := by
  intro z
  obtain ⟨y, hy⟩ := hg z
  obtain ⟨x, hx⟩ := hf y
  refine ⟨x, ?_⟩
  rw [congrFun (pointsMap_comp B S hS F f g) x]
  simp only [Function.comp_apply, hx, hy]

/-- **Stacks 040Y, (5) implies (8).** If the base change of `f` along a surjective étale chart
`V` of its target is locally of finite type, then a surjective étale chart square of `f` with
`V` as its chart of the target has the property: take any chart of the fibre product. -/
theorem holdsOnSurjectiveEtaleChart_of_targetAtlas (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y)
    (hgSurj : IsSurjective B S hS g) (hgEtale : IsEtale B S hS g)
    (hproj : IsLocallyOfFiniteType B S hS (pullback.fst g f)) :
    HoldsOnSurjectiveEtaleChart B S hS
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) f := by
  have hValg := isAlgebraicSpace_yoneda B S hS V
  have hPalg : IsAlgebraicSpace B S hS (Limits.pullback g f) :=
    isAlgebraicSpace_pullback B S hS g f hValg hX hY
  have hpb := AlgebraicSpaces.isPullback_fiberProduct B S hS
    (ObjectProperty.homMk g : (⟨yoneda.obj V, hValg⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
    (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
  have hqEtale : IsEtale B S hS (pullback.snd g f) :=
    isEtale_of_isPullback B S hS _ _ _ _ hpb hgEtale
  have hqSurj : IsSurjective B S hS (pullback.snd g f) :=
    isSurjective_of_isPullback B S hS hpb hgSurj
  obtain ⟨U, a, haSurj, haEtale⟩ := hPalg.exists_atlas
  set α : U ⟶ V := yoneda.preimage (a ≫ pullback.fst g f) with hαdef
  have hα : yoneda.map α = a ≫ pullback.fst g f := yoneda.map_preimage _
  have htop : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map α) :=
    hproj U V a (𝟙 (yoneda.obj V)) α haEtale (presheaf_etale_id B S hS V)
      (by rw [Category.comp_id, hα])
  have hmul := isMultiplicative_presheaf_etale B S hS
  have haIsEtale : IsEtale B S hS a := isEtale_of_presheaf_etale B S hS haEtale
  have haIsSurj : IsSurjective B S hS a :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS (Limits.pullback g f) hPalg U a).1 haSurj
  refine ⟨U, V, a ≫ pullback.snd g f, g, α,
    presheaf_etale_of_isEtale B S hS (isEtale_comp B S hS haIsEtale hqEtale),
    presheaf_etale_of_isEtale B S hS hgEtale,
    (presheafSurjective_iff_isSurjective_yoneda B S hS X hX U
      (a ≫ pullback.snd g f)).2 (isSurjective_comp_aux B S hS haIsSurj hqSurj), ?_, htop⟩
  rw [hα, Category.assoc, Category.assoc, pullback.condition]

/-- **Stacks 040Y, (6) implies (8).** If `f` becomes locally of finite type after
precomposition with a surjective étale chart `φ` of its source, then a surjective étale chart
square of the composite, composed with `φ`, is one of `f`. -/
theorem holdsOnSurjectiveEtaleChart_of_sourceAtlas (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (U₀ : BigFppfOver B S hS) (φ : yoneda.obj U₀ ⟶ X)
    (hφSurj : IsSurjective B S hS φ) (hφEtale : IsEtale B S hS φ)
    (hcomp : IsLocallyOfFiniteType B S hS (φ ≫ f)) :
    HoldsOnSurjectiveEtaleChart B S hS
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) f := by
  have hU₀ := isAlgebraicSpace_yoneda B S hS U₀
  obtain ⟨V, b, hbSurj, hbEtale⟩ := hY.exists_atlas
  have hproj := isLocallyOfFiniteType_pullback_fst' B S hS hU₀ hY
    (isAlgebraicSpace_yoneda B S hS V) (φ ≫ f) b hcomp
  obtain ⟨U, V', a, b', α, haE, hb'E, haS, hcomm, htop⟩ :=
    holdsOnSurjectiveEtaleChart_of_targetAtlas B S hS hU₀ hY (φ ≫ f) V b
      ((presheafSurjective_iff_isSurjective_yoneda B S hS Y hY V b).1 hbSurj)
      (isEtale_of_presheaf_etale B S hS hbEtale) hproj
  have hmul := isMultiplicative_presheaf_etale B S hS
  have haIsEtale : IsEtale B S hS a := isEtale_of_presheaf_etale B S hS haE
  have haIsSurj : IsSurjective B S hS a :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS (yoneda.obj U₀) hU₀ U a).1 haS
  refine ⟨U, V', a ≫ φ, b', α,
    presheaf_etale_of_isEtale B S hS (isEtale_comp B S hS haIsEtale hφEtale), hb'E,
    (presheafSurjective_iff_isSurjective_yoneda B S hS X hX U (a ≫ φ)).2
      (isSurjective_comp_aux B S hS haIsSurj hφSurj), ?_, htop⟩
  exact hcomm.trans (Category.assoc _ _ _).symm

/-! ### Stacks 040Y -/

/-- **Stacks 040Y.** For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` the
following nine conditions are equivalent: `f` is locally of finite type; `f` is of finite type
at every point of `X`; the base change of `f` along every morphism from a scheme over `S` is
locally of finite type; the same for every morphism from an affine scheme over `S`; the base
change of `f` along some surjective étale chart of `Y` is locally of finite type; the
composite of `f` with some surjective étale chart of `X` is locally of finite type; every
commuting square of étale charts of `f` induces a scheme morphism which is locally of finite
type; some such square whose chart of `X` is surjective does; and there are Zariski coverings
of `Y` and of the inverse images in `X` of its members over which `f` is locally of finite
type.

The conditions are listed in the order of the source, so the `n`-th entry of the list is
condition `(n)`. Schemes over `Y` are objects of the big fppf site of `S`, and condition (7)
is literally the definition of local finite type, which is why (1) ⇔ (7) is `Iff.rfl`. -/
@[stacks 040Y "all nine conditions (1)–(9) equivalent"]
theorem isLocallyOfFiniteType_tfae (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    List.TFAE
      [IsLocallyOfFiniteType B S hS f,
       (∀ x : points B S hS X, IsFiniteTypeAt B S hS f x),
       (∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
          IsLocallyOfFiniteType B S hS (pullback.fst g f)),
       (∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
          IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
            IsLocallyOfFiniteType B S hS (pullback.fst g f)),
       (∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y), IsSurjective B S hS g ∧
          IsEtale B S hS g ∧ IsLocallyOfFiniteType B S hS (pullback.fst g f)),
       (∃ (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ X), IsSurjective B S hS g ∧
          IsEtale B S hS g ∧ IsLocallyOfFiniteType B S hS (g ≫ f)),
       HoldsOnEveryEtaleChart B S hS
         (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) f,
       HoldsOnSurjectiveEtaleChart B S hS
         (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) f,
       (∃ (I : Type u) (Yᵢ : I → Subfunctor Y), IsZariskiCover B S hS I Yᵢ ∧
          ∀ i, ∃ (J : Type u) (Xᵢⱼ : J → Subfunctor ((Yᵢ i).preimage f).toFunctor),
            IsZariskiCover B S hS J Xᵢⱼ ∧
              ∀ j, IsLocallyOfFiniteType B S hS
                ((Xᵢⱼ j).ι ≫ (Yᵢ i).fromPreimage f))] := by
  tfae_have 1 ↔ 7 := Iff.rfl
  tfae_have 7 ↔ 8 := holdsOnEveryEtaleChart_iff_surjectiveChart B S hS
    (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget hX hY f
  tfae_have 1 → 2 := isFiniteTypeAt_of_isLocallyOfFiniteType B S hS hX hY f
  tfae_have 2 → 1 := isLocallyOfFiniteType_of_isFiniteTypeAt B S hS hX hY f
  tfae_have 1 → 3 := fun hf Z g ↦ isLocallyOfFiniteType_pullback_fst' B S hS hX hY
    (isAlgebraicSpace_yoneda B S hS Z) f g hf
  tfae_have 3 → 1 := isLocallyOfFiniteType_of_pullback_fst B S hS hX hY f
  tfae_have 3 → 4 := fun h Z g _ ↦ h Z g
  tfae_have 4 → 1 := isLocallyOfFiniteType_of_pullback_fst_of_isAffine B S hS hX hY f
  tfae_have 1 → 5 := exists_targetAtlas_isLocallyOfFiniteType B S hS hX hY f
  tfae_have 5 → 8 := fun h ↦ by
    obtain ⟨V, g, hs, he, hp⟩ := h
    exact holdsOnSurjectiveEtaleChart_of_targetAtlas B S hS hX hY f V g hs he hp
  tfae_have 1 → 6 := exists_sourceAtlas_isLocallyOfFiniteType B S hS hX hY f
  tfae_have 6 → 8 := fun h ↦ by
    obtain ⟨U, φ, hs, he, hp⟩ := h
    exact holdsOnSurjectiveEtaleChart_of_sourceAtlas B S hS hX hY f U φ hs he hp
  tfae_have 1 → 9 := exists_zariskiCover_isLocallyOfFiniteType B S hS hX hY f
  tfae_have 9 → 2 := isFiniteTypeAt_of_zariskiCover B S hS hX hY f
  tfae_finish

end AlgebraicGeometry.Space

end
