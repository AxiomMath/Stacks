module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ChowFiniteType.ModuleSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.ClosedImmersionMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedMorphismDiagonalDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.SelfProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.PhCoveringSeparatedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenLiftOverHenselianPair

/-!
# Properness of a morphism descends to a stage of a limit of bases

Let `B = lim B_i` be a directed inverse limit of algebraic spaces with affine transition
morphisms, let `f₀ : X₀ ⟶ Y₀` be a morphism of quasi-compact quasi-separated algebraic spaces
over `B₀`, and let `f_i : X_i ⟶ Y_i` and `f : X ⟶ Y` be the base changes of `f₀` to `B_i` and
to `B`, as recorded by `AlgebraicGeometry.Space.MorphismDescentSituation`. If the system of
bases satisfies `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`, `f` is proper and `f₀` is
locally of finite type, then `f_i` is proper for some stage `i`.

## Main results

* `MorphismDescentSituation.exists_isProper_mapAt_of_siteContainsBaseChangeLimits`: if `f` is
  proper and `f₀` is locally of finite type, then `f_i` is proper for some stage `i`; and
  `MorphismDescentSituation.exists_isProper_mapAt`, the same for a system small for the site.
* `MorphismDescentSituation.isFiniteType_mapAt`: if `f₀` is locally of finite type then `f_i` is
  of finite type, for every stage `i`.
* `MorphismDescentSituation.isProper_mapAt_of_le`: properness of `f_i` passes to every later
  stage.
* `MorphismDescentSituation.exists_isProper_mapAt_iff_exists_universallyClosed_mapAt`: if `f` is
  proper and `f₀` is locally of finite type, then `f_i` is proper for some stage `i` if and only
  if `f_i` is universally closed for some stage `i`.
* `MorphismDescentSituation.baseChangeTarget` and
  `MorphismDescentSituation.universallyClosed_mapAt_of_baseChangeTarget`: the situation base
  changed along a morphism `v : T₀ ⟶ Y₀`, and the descent of universal closedness at a stage
  along it when `v` is surjective and étale.
* `AlgebraicGeometry.Space.universallyClosed_of_etale_cover`: universal closedness may be
  tested after base change along a surjective étale morphism whose source is an algebraic space.
* `MorphismDescentSituation.exists_isPullback_mapAt_of_snd` and
  `MorphismDescentSituation.exists_isPullback_mapLimit_of_snd`: `f_j`, respectively `f`, is a
  base change of `f_i` along any morphism of the targets compatible with their projections to
  `Y₀`.

## References

* [Stacks Project, Tag 08K1](https://stacks.math.columbia.edu/tag/08K1)
* [Stacks Project, Tag 084W](https://stacks.math.columbia.edu/tag/084W)
* [Stacks Project, Tag 0851](https://stacks.math.columbia.edu/tag/0851)
* [Stacks Project, Tag 0850](https://stacks.math.columbia.edu/tag/0850)
* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 081F](https://stacks.math.columbia.edu/tag/081F)
* [Stacks Project, Tag 08AJ](https://stacks.math.columbia.edu/tag/08AJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### Properness of a representable morphism and of its base changes -/

section Representable

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Properness of the second leg of a cartesian square depends only on the cospan: two
cartesian squares over one cospan have isomorphic second legs. -/
theorem isProper_snd_of_isPullback_of_isPullback
    {W W' X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : W ⟶ X} {b : W ⟶ Y} {a' : W' ⟶ X} {b' : W' ⟶ Y} (f : X ⟶ Z) (g : Y ⟶ Z)
    (sq : IsPullback a b f g) (sq' : IsPullback a' b' f g) (h : IsProper B S hS b) :
    IsProper B S hS b' := by
  have he : (IsPullback.isoIsPullback _ _ sq' sq).hom ≫ b = b' :=
    IsPullback.isoIsPullback_hom_snd _ _ sq' sq
  rw [← he]
  exact (isProper_isIso_comp_iff B S hS (IsPullback.isoIsPullback _ _ sq' sq).hom b).mpr h

/-- The base change of `yoneda.map w` along `yoneda.map k` is proper if and only if the base
change of the underlying morphism of schemes of `w` along that of `k` is proper. -/
theorem isProper_pullback_snd_yoneda_map_iff {V W W' : BigFppfOver B S hS}
    (w : V ⟶ W) (k : W' ⟶ W) :
    IsProper B S hS (pullback.snd (yoneda.map w) (yoneda.map k)) ↔
      _root_.AlgebraicGeometry.IsProper
        (pullback.snd ((BigFppfOver.toScheme B S hS).map w)
          ((BigFppfOver.toScheme B S hS).map k)) := by
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hsite : IsPullback (pullback.fst w k) (pullback.snd w k) w k :=
    IsPullback.of_hasPullback w k
  have hy := hsite.map (yoneda (C := BigFppfOver B S hS))
  have hsch := hsite.map (BigFppfOver.toScheme B S hS)
  constructor
  · intro h
    have h1 : IsProper B S hS (yoneda.map (pullback.snd w k)) :=
      isProper_snd_of_isPullback_of_isPullback B S hS _ _ (IsPullback.of_hasPullback _ _) hy h
    exact (prop_snd_iff_of_isPullback
      (@_root_.AlgebraicGeometry.IsProper.{u} : MorphismProperty Scheme.{u}) hsch
      (IsPullback.of_hasPullback _ _)).mp ((isProper_yoneda_map_iff B S hS _).mp h1)
  · intro h
    have h2 := (prop_snd_iff_of_isPullback
      (@_root_.AlgebraicGeometry.IsProper.{u} : MorphismProperty Scheme.{u})
      (IsPullback.of_hasPullback _ _) hsch).mp h
    exact isProper_snd_of_isPullback_of_isPullback B S hS _ _ hy (IsPullback.of_hasPullback _ _)
      ((isProper_yoneda_map_iff B S hS _).mpr h2)

end Representable

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})}

/-- A cartesian square of presheaves whose four corners are algebraic spaces over `S`, read in
the category of algebraic spaces over `S`. -/
theorem isPullback_objectProperty_homMk
    {W X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ' : IsAlgebraicSpace B S hS Z)
    {a : W ⟶ X} {b : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback a b f g) :
    IsPullback
      (ObjectProperty.homMk a : (⟨W, hW⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)
      (ObjectProperty.homMk b : (⟨W, hW⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
      (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ'⟩)
      (ObjectProperty.homMk g : (⟨Y, hY⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ'⟩) :=
  IsPullback.of_map_of_faithful (F := ObjectProperty.ι _) sq

/-- Properness transfers along an arbitrary cartesian square of algebraic spaces over `S`, from
the morphism along which one base changes to the resulting projection. -/
theorem isProper_of_isPullback' {W X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ' : IsAlgebraicSpace B S hS Z)
    {a : W ⟶ X} {b : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback a b f g)
    (hf : IsProper B S hS f) :
    IsProper B S hS b :=
  (isProper_isStableUnderBaseChange B S hS).of_isPullback
    (isPullback_objectProperty_homMk hW hX hY hZ' sq) hf

/-- Being locally of finite type transfers along an arbitrary cartesian square of algebraic
spaces over `S`. -/
theorem isLocallyOfFiniteType_of_isPullback'
    {W X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ' : IsAlgebraicSpace B S hS Z)
    {a : W ⟶ X} {b : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback a b f g)
    (hf : IsLocallyOfFiniteType B S hS f) :
    IsLocallyOfFiniteType B S hS b :=
  (isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback
    (isPullback_objectProperty_homMk hW hX hY hZ' sq) hf

/-- If the base change of `f : X ⟶ Y` along a surjective étale morphism `φ : V ⟶ Y` whose source
is an algebraic space over `S` is universally closed, then `f` is universally closed. -/
theorem universallyClosed_of_etale_cover {X Y V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hV : IsAlgebraicSpace B S hS V) (f : X ⟶ Y) (φ : V ⟶ Y)
    (hφsurj : IsSurjective B S hS φ) (hφetale : IsEtale B S hS φ)
    (h : UniversallyClosed B S hS (pullback.fst φ f)) :
    UniversallyClosed B S hS f := by
  obtain ⟨W, a, hasurj, haetale⟩ := hV.exists_atlas
  have ha : IsSurjective B S hS a :=
    (surjective_iff_surjective_pointsMap B S hS V hV W a).mp hasurj
  have hae : IsEtale B S hS a := isEtale_of_presheaf_etale B S hS haetale
  exact universallyClosed_of_etale_atlas B S hS hY f W (a ≫ φ)
    (isSurjective_comp B S hS ha hφsurj) (isEtale_comp B S hS hae hφetale)
    (universallyClosed_of_isPullback B S hS
      (isAlgebraicSpace_pullback B S hS (a ≫ φ) f (isAlgebraicSpace_yoneda B S hS W) hX hY)
      (isAlgebraicSpace_pullback B S hS φ f hV hX hY)
      (isAlgebraicSpace_yoneda B S hS W) hV
      (pullback.fst φ f) a h
      (IsPullback.of_bot' (IsPullback.of_hasPullback (a ≫ φ) f)
        (IsPullback.of_hasPullback φ f)))

/-- If `f'` is a base change of `f` along a surjective étale morphism `φ` from an algebraic
space, and `f'` is universally closed, then so is `f`. -/
theorem universallyClosed_of_isPullback_etale_cover
    {X Y V X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hV : IsAlgebraicSpace B S hS V) (hX' : IsAlgebraicSpace B S hS X')
    (f : X ⟶ Y) (φ : V ⟶ Y)
    (hφsurj : IsSurjective B S hS φ) (hφetale : IsEtale B S hS φ)
    {ψ : X' ⟶ X} {f' : X' ⟶ V} (sq : IsPullback ψ f' f φ)
    (h : UniversallyClosed B S hS f') :
    UniversallyClosed B S hS f := by
  refine universallyClosed_of_etale_cover hX hY hV f φ hφsurj hφetale ?_
  have e : pullback.fst φ f = sq.flip.isoPullback.inv ≫ f' :=
    (Iso.eq_inv_comp _).mpr sq.flip.isoPullback_hom_fst
  rw [e]
  exact universallyClosed_comp B S hS hX' hV _ _
    (universallyClosed_of_isIso B S hS _) h

/-- A cartesian square is unchanged by rewriting its bottom edge along an equality of
morphisms. -/
theorem isPullback_of_eq_bottom {W X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : W ⟶ X} {b : W ⟶ Y} {f : X ⟶ Z} {g g' : Y ⟶ Z}
    (sq : IsPullback a b f g) (e : g = g') : IsPullback a b f g' := e ▸ sq

/-- For `t : W ⟶ Z`, `a : X ⟶ Y` and `x : Y ⟶ Z`, the fibre product `W ×_Z X` formed along
`a ≫ x` is, through its second projection, a fibre product `X ×_Y (W ×_Z Y)`. -/
theorem exists_isPullback_snd_of_comp_right {W X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (t : W ⟶ Z) (a : X ⟶ Y) (x : Y ⟶ Z) :
    ∃ β : pullback t (a ≫ x) ⟶ pullback t x,
      IsPullback (pullback.snd t (a ≫ x)) β a (pullback.snd t x) :=
  ⟨_, (IsPullback.of_right' (IsPullback.of_hasPullback t (a ≫ x))
    (IsPullback.of_hasPullback t x)).flip⟩

/-- If a square over `f₀` along `c` is cartesian and `β ≫ g = c`, then the cartesian square over
`f₀` along `g` yields a cartesian square over `β`. -/
private theorem exists_isPullback_of_comp_eq {P P' X Y Y' Y'' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : P ⟶ X} {m : P ⟶ Y'} {p' : P' ⟶ X} {m' : P' ⟶ Y''} {f₀ : X ⟶ Y} {c : Y' ⟶ Y}
    {g : Y'' ⟶ Y} (β : Y' ⟶ Y'') (hs : IsPullback p m f₀ c) (hβ : β ≫ g = c)
    (sq : IsPullback p' m' f₀ g) : ∃ α : P ⟶ P', IsPullback α m m' β :=
  ⟨_, IsPullback.of_right' (isPullback_of_eq_bottom hs hβ.symm) sq⟩

/-- Pasting the square of the base change along `v` with a square over `f₀` base changes the
latter along a base change of `v`. -/
private theorem exists_isPullback_paste_comp_right
    {A Z X Y T SD : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (b : A ⟶ Z) (s : X ⟶ Z) (g : Y ⟶ Z) (f₀ : X ⟶ Y) (v : T ⟶ Y) {p : SD ⟶ X}
    {m : SD ⟶ pullback b g}
    {m' : pullback b (pullback.fst f₀ v ≫ s) ⟶ pullback b (v ≫ g)}
    (hD' : IsPullback (pullback.snd b (pullback.fst f₀ v ≫ s)) m' (pullback.snd f₀ v)
      (pullback.snd b (v ≫ g)))
    (hD : IsPullback p m f₀ (pullback.snd b g)) :
    ∃ (β : pullback b (v ≫ g) ⟶ pullback b g)
      (ψ : pullback b (pullback.fst f₀ v ≫ s) ⟶ SD),
      IsPullback ψ m' m β ∧ IsPullback (pullback.snd b (v ≫ g)) β v (pullback.snd b g) := by
  obtain ⟨β, sq⟩ := exists_isPullback_snd_of_comp_right b v g
  obtain ⟨ψ, h⟩ := exists_isPullback_of_comp_eq β
    (hD'.paste_horiz (IsPullback.of_hasPullback f₀ v)) sq.w.symm hD
  exact ⟨β, ψ, h, sq⟩

namespace MorphismDescentSituation

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : MorphismDescentSituation B S hS hZ I)

/-- For stages `i, j` and a morphism `β` from the target at `j` to the target at `i` compatible
with their projections to `Y₀`, the base change `f_j` is a base change of `f_i` along `β`. -/
theorem exists_isPullback_mapAt_of_snd {i j : I} (hi : D.initial ≤ i) (hj : D.initial ≤ j)
    (β : D.targetAt j hj ⟶ D.targetAt i hi)
    (hβ : β ≫ pullback.snd (D.baseAtToInitial i hi) D.targetToBase =
      pullback.snd (D.baseAtToInitial j hj) D.targetToBase) :
    ∃ α : D.sourceAt j hj ⟶ D.sourceAt i hi,
      IsPullback α (D.mapAt j hj) (D.mapAt i hi) β := by
  exact exists_isPullback_of_comp_eq β (D.isPullback_mapAt j hj) hβ (D.isPullback_mapAt i hi)

/-- The base change of `f₀` to the limit is a base change of its base change to a stage along
any comparison morphism of the targets compatible with their projections to `Y₀`. -/
theorem exists_isPullback_mapLimit_of_snd (i : I) (hi : D.initial ≤ i)
    (β : D.targetLimit ⟶ D.targetAt i hi)
    (hβ : β ≫ pullback.snd (D.baseAtToInitial i hi) D.targetToBase =
      pullback.snd (limit.π D.base (op D.initial)) D.targetToBase) :
    ∃ α : D.sourceLimit ⟶ D.sourceAt i hi,
      IsPullback α D.mapLimit (D.mapAt i hi) β := by
  exact exists_isPullback_of_comp_eq β D.isPullback_mapLimit hβ (D.isPullback_mapAt i hi)

/-! ### Finiteness at every stage -/

/-- The base change `f_i` of `f₀` to any stage `i` is quasi-compact. -/
theorem isQuasiCompact_mapAt (i : I) (hi : D.initial ≤ i) :
    IsQuasiCompact B S hS (D.mapAt i hi) :=
  isQuasiCompact_of_isQuasiCompactSpace B S hS hZ (D.targetAt_isAlgebraicSpace i hi)
    (D.isAbsolutelyQuasiSeparated_targetAt i hi) (D.isQuasiCompactSpace_sourceAt i hi)
    (D.mapAt i hi)

/-- If `f₀` is locally of finite type then its base change `f_i` to any stage is of finite
type. -/
theorem isFiniteType_mapAt (hf₀ : IsLocallyOfFiniteType B S hS D.map₀)
    (i : I) (hi : D.initial ≤ i) :
    IsFiniteType B S hS (D.mapAt i hi) :=
  ⟨D.isLocallyOfFiniteType_mapAt hf₀ i hi, D.isQuasiCompact_mapAt i hi⟩

/-! ### Permanence along the stages -/

/-- Being locally of finite type passes from a stage to every later stage. -/
theorem isLocallyOfFiniteType_mapAt_of_le {i j : I} (hi : D.initial ≤ i) (hij : i ≤ j)
    (h : IsLocallyOfFiniteType B S hS (D.mapAt i hi)) :
    IsLocallyOfFiniteType B S hS (D.mapAt j (hi.trans hij)) := by
  obtain ⟨α, β, hpb⟩ := D.exists_isPullback_mapAt_of_le hi hij
  exact isLocallyOfFiniteType_of_isPullback'
    (D.sourceAt_isAlgebraicSpace j (hi.trans hij)) (D.sourceAt_isAlgebraicSpace i hi)
    (D.targetAt_isAlgebraicSpace j (hi.trans hij)) (D.targetAt_isAlgebraicSpace i hi)
    hpb h

/-- Separatedness of the base change of `f₀` passes from a stage to every later stage. -/
theorem isSeparated_mapAt_of_le {i j : I} (hi : D.initial ≤ i) (hij : i ≤ j)
    (h : IsSeparated B S hS (D.mapAt i hi)) :
    IsSeparated B S hS (D.mapAt j (hi.trans hij)) := by
  obtain ⟨α, β, hpb⟩ := D.exists_isPullback_mapAt_of_le hi hij
  rw [← hpb.isoPullback_hom_snd]
  exact isSeparated_comp B S hS _ _ (isSeparated_of_isIso B S hS _)
    (isSeparated_pullback B S hS (D.mapAt i hi) β h)

/-- Universal closedness of the base change of `f₀` passes from a stage to every later
stage. -/
theorem universallyClosed_mapAt_of_le {i j : I} (hi : D.initial ≤ i) (hij : i ≤ j)
    (h : UniversallyClosed B S hS (D.mapAt i hi)) :
    UniversallyClosed B S hS (D.mapAt j (hi.trans hij)) := by
  obtain ⟨α, β, hpb⟩ := D.exists_isPullback_mapAt_of_le hi hij
  exact universallyClosed_of_isPullback B S hS
    (D.sourceAt_isAlgebraicSpace j (hi.trans hij)) (D.sourceAt_isAlgebraicSpace i hi)
    (D.targetAt_isAlgebraicSpace j (hi.trans hij)) (D.targetAt_isAlgebraicSpace i hi)
    (D.mapAt i hi) β h hpb.flip

/-- Properness of the base change of `f₀` passes from a stage to every later stage. -/
theorem isProper_mapAt_of_le {i j : I} (hi : D.initial ≤ i) (hij : i ≤ j)
    (h : IsProper B S hS (D.mapAt i hi)) :
    IsProper B S hS (D.mapAt j (hi.trans hij)) :=
  ⟨D.isSeparated_mapAt_of_le hi hij h.1,
    ⟨D.isLocallyOfFiniteType_mapAt_of_le hi hij h.2.1.1,
      D.isQuasiCompact_mapAt j (hi.trans hij)⟩,
    D.universallyClosed_mapAt_of_le hi hij h.2.2⟩

/-! ### Reduction to universal closedness -/

/-- If the base change `f` of `f₀` to the limit `B` is separated and `f₀` is locally of finite
type, then the base change `f_i` of `f₀` to some stage `B_i` is separated and of finite type. -/
theorem exists_isSeparated_isFiniteType_mapAt
    (hconv : SiteContainsBaseChangeLimits B S hS D.base) (hf : IsSeparated B S hS D.mapLimit)
    (hf₀ : IsLocallyOfFiniteType B S hS D.map₀) :
    ∃ (i : I) (hi : D.initial ≤ i),
      IsSeparated B S hS (D.mapAt i hi) ∧ IsFiniteType B S hS (D.mapAt i hi) := by
  obtain ⟨i, hi, hsep⟩ := D.exists_isSeparated_mapAt_of_siteContainsBaseChangeLimits hconv hf
  exact ⟨i, hi, hsep, D.isFiniteType_mapAt hf₀ i hi⟩

/-- A stage at which the base change of `f₀` is separated and universally closed is one at
which it is proper, as soon as `f₀` is locally of finite type. -/
theorem isProper_mapAt_of_universallyClosed (hf₀ : IsLocallyOfFiniteType B S hS D.map₀)
    (i : I) (hi : D.initial ≤ i) (hsep : IsSeparated B S hS (D.mapAt i hi))
    (huc : UniversallyClosed B S hS (D.mapAt i hi)) :
    IsProper B S hS (D.mapAt i hi) :=
  ⟨hsep, D.isFiniteType_mapAt hf₀ i hi, huc⟩

/-- If `f` is proper, `f₀` is locally of finite type, and `f_i` is universally closed for some
stage `i`, then `f_j` is proper for some stage `j`. -/
theorem exists_isProper_mapAt_of_exists_universallyClosed_mapAt
    (hconv : SiteContainsBaseChangeLimits B S hS D.base) (hf : IsProper B S hS D.mapLimit)
    (hf₀ : IsLocallyOfFiniteType B S hS D.map₀)
    (huc : ∃ (i : I) (hi : D.initial ≤ i), UniversallyClosed B S hS (D.mapAt i hi)) :
    ∃ (j : I) (hj : D.initial ≤ j), IsProper B S hS (D.mapAt j hj) := by
  obtain ⟨i₁, hi₁, hsep⟩ := D.exists_isSeparated_mapAt_of_siteContainsBaseChangeLimits hconv hf.1
  obtain ⟨i₂, hi₂, hclosed⟩ := huc
  obtain ⟨k, hk₁, hk₂⟩ := exists_ge_ge i₁ i₂
  exact ⟨k, hi₁.trans hk₁, D.isProper_mapAt_of_universallyClosed hf₀ k (hi₁.trans hk₁)
    (D.isSeparated_mapAt_of_le hi₁ hk₁ hsep)
    (D.universallyClosed_mapAt_of_le hi₂ hk₂ hclosed)⟩

/-- If `f` is proper and `f₀` is locally of finite type, then `f_i` is proper for some stage `i`
if and only if `f_i` is universally closed for some stage `i`. -/
theorem exists_isProper_mapAt_iff_exists_universallyClosed_mapAt
    (hconv : SiteContainsBaseChangeLimits B S hS D.base) (hf : IsProper B S hS D.mapLimit)
    (hf₀ : IsLocallyOfFiniteType B S hS D.map₀) :
    (∃ (i : I) (hi : D.initial ≤ i), IsProper B S hS (D.mapAt i hi)) ↔
      ∃ (i : I) (hi : D.initial ≤ i), UniversallyClosed B S hS (D.mapAt i hi) :=
  ⟨fun ⟨i, hi, h⟩ => ⟨i, hi, h.2.2⟩,
    D.exists_isProper_mapAt_of_exists_universallyClosed_mapAt hconv hf hf₀⟩

/-! ### Base changing the whole situation along a morphism to the target -/

section BaseChangeTarget

variable {T₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (v : T₀ ⟶ D.target₀)
  (hT : IsAlgebraicSpace B S hS T₀) (hTqc : IsQuasiCompactSpace B S hS T₀)
  (hTqs : IsAbsolutelyQuasiSeparated B S hS hZ T₀)

/-- The situation base changed along a morphism `v : T₀ ⟶ Y₀` to the target: the system of
bases and the distinguished stage are unchanged, and the morphism to be descended is replaced by
its base change `X₀ ×_{Y₀} T₀ ⟶ T₀`. -/
noncomputable def baseChangeTarget : MorphismDescentSituation B S hS hZ I where
  base := D.base
  base_isAlgebraicSpace := D.base_isAlgebraicSpace
  transition_affine := D.transition_affine
  limit_isAlgebraicSpace := D.limit_isAlgebraicSpace
  initial := D.initial
  source₀ := pullback D.map₀ v
  target₀ := T₀
  sourceToBase := pullback.fst D.map₀ v ≫ D.sourceToBase
  targetToBase := v ≫ D.targetToBase
  map₀ := pullback.snd D.map₀ v
  map₀_over := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc, D.map₀_over]
  source₀_isAlgebraicSpace := isAlgebraicSpace_pullback B S hS D.map₀ v
    D.source₀_isAlgebraicSpace hT D.target₀_isAlgebraicSpace
  target₀_isAlgebraicSpace := hT
  base₀_quasiCompact := D.base₀_quasiCompact
  base₀_quasiSeparated := D.base₀_quasiSeparated
  source₀_quasiCompact := isQuasiCompactSpace_pullback B S hS hZ D.map₀ v
    D.source₀_isAlgebraicSpace D.target₀_isAlgebraicSpace D.source₀_quasiCompact hTqc
    D.target₀_quasiSeparated
  source₀_quasiSeparated := isAbsolutelyQuasiSeparated_pullback B S hS hZ D.map₀ v
    D.source₀_isAlgebraicSpace hT D.target₀_isAlgebraicSpace D.source₀_quasiSeparated hTqs
  target₀_quasiCompact := hTqc
  target₀_quasiSeparated := hTqs

/-- At every stage, the base-changed situation's morphism is a base change of the original
situation's, along a base change of `v`. -/
theorem exists_isPullback_mapAt_baseChangeTarget (i : I) (hi : D.initial ≤ i) :
    ∃ (β : (D.baseChangeTarget v hT hTqc hTqs).targetAt i hi ⟶ D.targetAt i hi)
      (ψ : (D.baseChangeTarget v hT hTqc hTqs).sourceAt i hi ⟶ D.sourceAt i hi),
      IsPullback ψ ((D.baseChangeTarget v hT hTqc hTqs).mapAt i hi) (D.mapAt i hi) β ∧
        IsPullback
          (pullback.snd (D.baseAtToInitial i hi)
            (D.baseChangeTarget v hT hTqc hTqs).targetToBase)
          β v (pullback.snd (D.baseAtToInitial i hi) D.targetToBase) := by
  exact exists_isPullback_paste_comp_right _ _ _ _ _
    ((D.baseChangeTarget v hT hTqc hTqs).isPullback_mapAt i hi) (D.isPullback_mapAt i hi)

/-- At the limit, the base-changed situation's morphism is a base change of the original
situation's, along the base change of `v` to the limit. -/
theorem exists_isPullback_mapLimit_baseChangeTarget :
    ∃ (β : (D.baseChangeTarget v hT hTqc hTqs).targetLimit ⟶ D.targetLimit)
      (ψ : (D.baseChangeTarget v hT hTqc hTqs).sourceLimit ⟶ D.sourceLimit),
      IsPullback ψ ((D.baseChangeTarget v hT hTqc hTqs).mapLimit) D.mapLimit β := by
  obtain ⟨β, ψ, sq, -⟩ := exists_isPullback_paste_comp_right _ _ _ _ _
    (D.baseChangeTarget v hT hTqc hTqs).isPullback_mapLimit D.isPullback_mapLimit
  exact ⟨β, ψ, sq⟩

/-- The base-changed situation's morphism to the limit is proper when the original situation's
is. -/
theorem isProper_mapLimit_baseChangeTarget (h : IsProper B S hS D.mapLimit) :
    IsProper B S hS ((D.baseChangeTarget v hT hTqc hTqs).mapLimit) := by
  obtain ⟨β, ψ, sq⟩ := D.exists_isPullback_mapLimit_baseChangeTarget v hT hTqc hTqs
  exact isProper_of_isPullback' (D.baseChangeTarget v hT hTqc hTqs).sourceLimit_isAlgebraicSpace
    D.sourceLimit_isAlgebraicSpace
    (D.baseChangeTarget v hT hTqc hTqs).targetLimit_isAlgebraicSpace
    D.targetLimit_isAlgebraicSpace sq h

/-- The base-changed situation's morphism at the distinguished stage is locally of finite type
when the original situation's is. -/
theorem isLocallyOfFiniteType_map₀_baseChangeTarget
    (h : IsLocallyOfFiniteType B S hS D.map₀) :
    IsLocallyOfFiniteType B S hS (D.baseChangeTarget v hT hTqc hTqs).map₀ :=
  isLocallyOfFiniteType_of_isPullback' (isAlgebraicSpace_pullback B S hS D.map₀ v
      D.source₀_isAlgebraicSpace hT D.target₀_isAlgebraicSpace)
    D.source₀_isAlgebraicSpace hT D.target₀_isAlgebraicSpace
    (IsPullback.of_hasPullback D.map₀ v) h

/-- If `v : T₀ ⟶ Y₀` is surjective and étale and the base-changed situation's morphism is
universally closed at a stage, then so is the original situation's morphism at that stage. -/
theorem universallyClosed_mapAt_of_baseChangeTarget
    (hvsurj : IsSurjective B S hS v) (hvetale : IsEtale B S hS v)
    (i : I) (hi : D.initial ≤ i)
    (h : UniversallyClosed B S hS ((D.baseChangeTarget v hT hTqc hTqs).mapAt i hi)) :
    UniversallyClosed B S hS (D.mapAt i hi) := by
  obtain ⟨β, ψ, sq, sq_tgt⟩ := D.exists_isPullback_mapAt_baseChangeTarget v hT hTqc hTqs i hi
  have hβsurj : IsSurjective B S hS β :=
    surjective_pointsMap_of_isPullback B S hS sq_tgt hvsurj
  have hβetale : IsEtale B S hS β :=
    isEtale_of_isPullback B S hS _ _ _ _
      (isPullback_objectProperty_homMk
        ((D.baseChangeTarget v hT hTqc hTqs).targetAt_isAlgebraicSpace i hi) hT
        (D.targetAt_isAlgebraicSpace i hi) D.target₀_isAlgebraicSpace sq_tgt)
      hvetale
  exact universallyClosed_of_isPullback_etale_cover
    (D.sourceAt_isAlgebraicSpace i hi) (D.targetAt_isAlgebraicSpace i hi)
    ((D.baseChangeTarget v hT hTqc hTqs).targetAt_isAlgebraicSpace i hi)
    ((D.baseChangeTarget v hT hTqc hTqs).sourceAt_isAlgebraicSpace i hi)
    (D.mapAt i hi) β hβsurj hβetale sq h

end BaseChangeTarget

/-! ### Descent of properness -/

/-- If the system of bases satisfies `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`, the
base change `f` of `f₀` to the limit `B` is proper and `f₀` is locally of finite type, then the
base change `f_i` of `f₀` to some stage `B_i` is proper. -/
@[sga "3 VIB 10.1" "Properness case of 10.1"]
theorem exists_isProper_mapAt_of_siteContainsBaseChangeLimits
    (hconv : SiteContainsBaseChangeLimits B S hS D.base) (hf : IsProper B S hS D.mapLimit)
    (hf₀ : IsLocallyOfFiniteType B S hS D.map₀) :
    ∃ (i : I) (hi : D.initial ≤ i), IsProper B S hS (D.mapAt i hi) := by
  classical
  refine (D.exists_isProper_mapAt_iff_exists_universallyClosed_mapAt hconv hf hf₀).mpr ?_
  obtain ⟨U, chart, hU, hchartS, hchartE⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS D.target₀
      D.target₀_isAlgebraicSpace).mp D.target₀_quasiCompact
  have hchartSurj : IsSurjective B S hS chart :=
    isSurjective_of_presheafSurjective B S hS chart hchartS
  have hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  have hT : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hTqc : IsQuasiCompactSpace B S hS (yoneda.obj U) :=
    isQuasiCompactSpace_yoneda_of_isAffine B S hS U hU
  have hTqs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj U) :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS (yoneda.obj U) hZ
      ⟨U, inferInstance, ⟨Functor.RepresentableBy.yoneda U⟩⟩
  set D' := D.baseChangeTarget chart hT hTqc hTqs
  suffices h : ∃ (m : I) (hm : D.initial ≤ m),
      UniversallyClosed B S hS (D'.mapAt m hm) by
    obtain ⟨m, hm, hucm⟩ := h
    exact ⟨m, hm, D.universallyClosed_mapAt_of_baseChangeTarget chart hT hTqc hTqs
      hchartSurj hchartE m hm hucm⟩
  have hfL : IsProper B S hS D'.mapLimit :=
    D.isProper_mapLimit_baseChangeTarget chart hT hTqc hTqs hf
  have hf₀' : IsLocallyOfFiniteType B S hS D'.map₀ :=
    D.isLocallyOfFiniteType_map₀_baseChangeTarget chart hT hTqc hTqs hf₀
  obtain ⟨i₀, hi₀, hsep₀⟩ :=
    D'.exists_isSeparated_mapAt_of_siteContainsBaseChangeLimits
      hconv hfL.1
  have : Nonempty I := ⟨D.initial⟩
  have : IsDirectedOrder I := inferInstance
  have : IsFiltered I := inferInstance
  have : IsCofiltered Iᵒᵖ := inferInstance
  have : IsCofiltered (Over (op D.initial)) := inferInstance
  set sys := affineChartSystem B S hS (op D.initial) D.base ⟨U, hU⟩
    (chart ≫ D.targetToBase) (fun {_ _} g ↦ D.transition_affine g) with hsys
  set br := AffineChartSystem.limitBridgeOfLimitInSite sys
    (sys.limitInSite_of_siteContainsBaseChangeLimits hconv) with hbr
  set j₀ : Over (op D.initial) := Over.mk (homOfLE hi₀).op with hj₀
  have hbaseMap : ∀ {j k : Over (op D.initial)} (g : j ⟶ k),
      yoneda.map (sys.siteDiagram.map g) ≫ sys.baseMap k = sys.baseMap j := by
    intro j k g
    have hnat : yoneda.map (sys.siteDiagram.map g) ≫ sys.iso.hom.app k =
        sys.iso.hom.app j ≫ (stageBaseChangeDiagram B S hS (op D.initial) D.base ⟨U, hU⟩
          (chart ≫ D.targetToBase)).map g := sys.iso.hom.naturality g
    simp only [AffineChartSystem.baseMap]
    rw [← Category.assoc, hnat, Category.assoc,
      stageBaseChangeDiagram_map_comp_snd B S hS (op D.initial) D.base ⟨U, hU⟩
        (chart ≫ D.targetToBase) g]
  set e₀ : yoneda.obj (sys.siteDiagram.obj j₀) ≅
      D'.targetAt i₀ hi₀ :=
    IsPullback.isoIsPullback _ _ (sys.isPullback j₀)
      (D'.targetAt_isPullback i₀ hi₀) with he₀
  set eL := IsPullback.isoIsPullback _ _ br.isPullback
    D'.targetLimit_isPullback with heL
  have he₀snd : e₀.hom ≫ pullback.snd
      (D'.baseAtToInitial i₀ hi₀)
      D'.targetToBase = sys.baseMap j₀ :=
    IsPullback.isoIsPullback_hom_snd _ _ (sys.isPullback j₀)
      (D'.targetAt_isPullback i₀ hi₀)
  have transfer : ∀ (Wj : BigFppfOver B S hS)
      (π : yoneda.obj Wj ⟶ yoneda.obj (sys.siteDiagram.obj j₀))
      (Tj : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (ej : yoneda.obj Wj ≅ Tj)
      (β : Tj ⟶ D'.targetAt i₀ hi₀),
      ej.hom ≫ β = π ≫ e₀.hom →
      ∀ (Xj : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (fj : Xj ⟶ Tj)
        {Vc : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (ρ : Vc ⟶
          D'.sourceAt i₀ hi₀)
        (wm : Vc ⟶ yoneda.obj (sys.siteDiagram.obj j₀))
        (α : Xj ⟶ D'.sourceAt i₀ hi₀),
        wm ≫ e₀.hom = ρ ≫ D'.mapAt i₀ hi₀ →
        IsPullback α fj (D'.mapAt i₀ hi₀) β →
        (IsProper B S hS (pullback.snd wm π) ↔ IsProper B S hS (pullback.snd ρ α ≫ fj)) := by
    intro Wj π Tj ej β hβ Xj fj Vc ρ wm α hwm sq
    have hB : IsPullback π ej.hom e₀.hom β := IsPullback.of_vert_isIso ⟨hβ.symm⟩
    have hA := (IsPullback.of_hasPullback wm π).paste_vert hB
    rw [hwm] at hA
    have hC := (IsPullback.of_hasPullback ρ α).paste_vert sq
    rw [← isProper_comp_isIso_iff B S hS (pullback.snd wm π) ej.hom]
    exact ⟨isProper_snd_of_isPullback_of_isPullback B S hS _ _ hA hC,
      isProper_snd_of_isPullback_of_isPullback B S hS _ _ hC hA⟩
  obtain ⟨V, ρ, hρp, hρs⟩ :=
    exists_properSurjective_schemeCover_of_isSeparated_isFiniteType_toAffine B S hS
      (sys.siteDiagram.obj j₀) (sys.isAffine_obj j₀)
      (D'.sourceAt_isAlgebraicSpace i₀ hi₀)
      (D'.mapAt i₀ hi₀ ≫ e₀.inv)
      ((isSeparated_comp_isIso_iff B S hS _ e₀.inv).mpr hsep₀)
      ((isFiniteType_comp_isIso_iff B S hS _ e₀.inv).mpr
        (D'.isFiniteType_mapAt hf₀' i₀ hi₀))
  set u := ρ ≫ D'.mapAt i₀ hi₀ with hu
  set w := yoneda.preimage (u ≫ e₀.inv) with hwdef
  have hwmap : yoneda.map w = u ≫ e₀.inv := yoneda.map_preimage _
  have hwe₀ : yoneda.map w ≫ e₀.hom = u := by
    rw [hwmap, Category.assoc, e₀.inv_hom_id, Category.comp_id]
  have step : ∀ {Wk : BigFppfOver B S hS} {Tk : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      {sk : Tk ⟶ D'.target₀}
      (ek : yoneda.obj Wk ≅ Tk) (π : yoneda.obj Wk ⟶ yoneda.obj (sys.siteDiagram.obj j₀))
      (bk : yoneda.obj Wk ⟶ _), ek.inv ≫ bk = sk → π ≫ sys.baseMap j₀ = bk →
      ∃ β : Tk ⟶ D'.targetAt i₀ hi₀,
        ek.hom ≫ β = π ≫ e₀.hom ∧ β ≫ pullback.snd
          (D'.baseAtToInitial i₀ hi₀)
          D'.targetToBase = sk := by
    intro Wk Tk sk ek π bk hek hπ
    refine ⟨ek.inv ≫ π ≫ e₀.hom, ?_, ?_⟩
    · rw [← Category.assoc, ek.hom_inv_id, Category.id_comp]
    · exact (Category.assoc _ _ _).trans ((congrArg (ek.inv ≫ ·)
        (((Category.assoc _ _ _).trans (congrArg (π ≫ ·) he₀snd)).trans hπ)).trans hek)
  obtain ⟨β, hβL, hβLsnd⟩ := step eL _ _
    (IsPullback.isoIsPullback_inv_snd _ _ br.isPullback
      D'.targetLimit_isPullback) (br.baseMap_comp j₀)
  obtain ⟨αL, sqL⟩ := D'.exists_isPullback_mapLimit_of_snd
    i₀ hi₀ _ hβLsnd
  have hρqc : IsQuasiCompact B S hS ρ := hρp.2.1.2
  have hVqc : IsQuasiCompactSpace B S hS (yoneda.obj V) :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS
      (D'.sourceAt_isAlgebraicSpace i₀ hi₀)
      (D'.isQuasiCompactSpace_sourceAt i₀ hi₀) hρqc
  have husep : IsSeparated B S hS u := by
    rw [hu]; exact isSeparated_comp B S hS _ _ hρp.1 hsep₀
  have huft : IsFiniteType B S hS u := by
    rw [hu]
    exact isFiniteType_comp B S hS (isAlgebraicSpace_yoneda B S hS V)
      (D'.sourceAt_isAlgebraicSpace i₀ hi₀)
      (D'.targetAt_isAlgebraicSpace i₀ hi₀) _ _
      hρp.2.1 (D'.isFiniteType_mapAt hf₀' i₀ hi₀)
  have hwsep : IsSeparated B S hS (yoneda.map w) := by
    rw [hwmap]
    exact (isSeparated_comp_isIso_iff B S hS u e₀.inv).mpr husep
  have hwft : IsFiniteType B S hS (yoneda.map w) := by
    rw [hwmap]
    exact (isFiniteType_comp_isIso_iff B S hS u e₀.inv).mpr huft
  have hVc : CompactSpace ((BigFppfOver.toScheme B S hS).obj V) :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS hVqc
  have hj₀aff : IsAffine ((BigFppfOver.toScheme B S hS).obj (sys.siteDiagram.obj j₀)) :=
    sys.isAffine_obj j₀
  have hj₀c : CompactSpace ((BigFppfOver.toScheme B S hS).obj (sys.siteDiagram.obj j₀)) :=
    Scheme.compactSpace_of_isAffine _
  have hj₀qs :
      QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj (sys.siteDiagram.obj j₀)) :=
    inferInstance
  have hwqs : _root_.AlgebraicGeometry.QuasiSeparated ((BigFppfOver.toScheme B S hS).map w) :=
    (isQuasiSeparated_yoneda_map_iff B S hS w).mp
      (isQuasiSeparated_of_isSeparated B S hS hwsep)
  have hVqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj V) :=
    quasiSeparatedSpace_of_quasiSeparated ((BigFppfOver.toScheme B S hS).map w)
  have hwlft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map w) :=
    (isLocallyOfFiniteType_yoneda_map_iff B S hS w).mp hwft.1
  have hAff : ∀ {a b : Over (op D.initial)} (g : a ⟶ b),
      _root_.AlgebraicGeometry.IsAffineHom (sys.schemeDiagram.map g) :=
    fun g ↦ sys.isAffineHom_map g
  have : CompactSpace (Over.mk ((BigFppfOver.toScheme B S hS).map w) :
      Over (sys.schemeDiagram.obj j₀)).left := hVc
  have : QuasiSeparatedSpace (Over.mk ((BigFppfOver.toScheme B S hS).map w) :
      Over (sys.schemeDiagram.obj j₀)).left := hVqs
  have : CompactSpace (sys.schemeDiagram.obj j₀) := hj₀c
  have : QuasiSeparatedSpace (sys.schemeDiagram.obj j₀) := hj₀qs
  have : CompactSpace (Over.mk (𝟙 (sys.schemeDiagram.obj j₀))).left := hj₀c
  have : QuasiSeparatedSpace (Over.mk (𝟙 (sys.schemeDiagram.obj j₀))).left := hj₀qs
  have : LocallyOfFiniteType (Over.homMk ((BigFppfOver.toScheme B S hS).map w)
      (Category.comp_id _) :
      (Over.mk ((BigFppfOver.toScheme B S hS).map w) : Over (sys.schemeDiagram.obj j₀)) ⟶
        Over.mk (𝟙 (sys.schemeDiagram.obj j₀))).left := hwlft
  have hPA := isAlgebraicSpace_pullback B S hS ρ αL (isAlgebraicSpace_yoneda B S hS V)
    D'.sourceLimit_isAlgebraicSpace (D'.sourceAt_isAlgebraicSpace i₀ hi₀)
  have hlimProper : IsProper B S hS (pullback.snd ρ αL ≫ D'.mapLimit) :=
    isProper_comp B S hS hPA D'.sourceLimit_isAlgebraicSpace D'.targetLimit_isAlgebraicSpace _ _
      (isProper_of_isPullback' hPA (isAlgebraicSpace_yoneda B S hS V)
        D'.sourceLimit_isAlgebraicSpace (D'.sourceAt_isAlgebraicSpace i₀ hi₀)
        (IsPullback.of_hasPullback ρ αL) hρp) hfL
  have hover : _root_.AlgebraicGeometry.IsProper
      ((Over.pullback (((BigFppfOver.toScheme B S hS).mapCone br.cone).π.app j₀)).map
        (Over.homMk ((BigFppfOver.toScheme B S hS).map w) (Category.comp_id _) :
          (Over.mk ((BigFppfOver.toScheme B S hS).map w) :
            Over (sys.schemeDiagram.obj j₀)) ⟶ Over.mk (𝟙 _))).left := by
    refine (prop_overPullback_map_left_iff_pullback_snd
      (@_root_.AlgebraicGeometry.IsProper.{u} : MorphismProperty Scheme.{u})
      ((BigFppfOver.toScheme B S hS).map w) _).mpr ?_
    refine (isProper_pullback_snd_yoneda_map_iff B S hS w (br.cone.π.app j₀)).mp ?_
    exact (transfer br.cone.pt (yoneda.map (br.cone.π.app j₀))
      D'.targetLimit eL _ hβL
      D'.sourceLimit
      D'.mapLimit ρ (yoneda.map w) αL hwe₀ sqL).mpr
      hlimProper
  obtain ⟨j, g, hstage⟩ := exists_isProper_baseChange_of_isLimit sys.schemeDiagram
    ((BigFppfOver.toScheme B S hS).mapCone br.cone) j₀ br.schemeIsLimit
    (Over.mk ((BigFppfOver.toScheme B S hS).map w)) (Over.mk (𝟙 _))
    (Over.homMk ((BigFppfOver.toScheme B S hS).map w) (Category.comp_id _))
  refine ⟨j.left.unop, leOfHom j.hom.unop, ?_⟩
  have hbase : D'.baseAtToInitial j.left.unop
      (leOfHom j.hom.unop) = D.base.map j.hom := congrArg D.base.map (Subsingleton.elim _ _)
  have hCj : IsPullback (sys.stageMap j) (sys.baseMap j)
      (D'.baseAtToInitial j.left.unop
        (leOfHom j.hom.unop)) D'.targetToBase := by
    rw [hbase]; exact sys.isPullback j
  set ej : yoneda.obj (sys.siteDiagram.obj j) ≅
      D'.targetAt j.left.unop (leOfHom j.hom.unop) :=
    IsPullback.isoIsPullback _ _ hCj
      (D'.targetAt_isPullback j.left.unop
        (leOfHom j.hom.unop)) with hej
  obtain ⟨β, hβj, hβjsnd⟩ := step ej _ _
    (IsPullback.isoIsPullback_inv_snd _ _ hCj
      (D'.targetAt_isPullback j.left.unop
        (leOfHom j.hom.unop))) (hbaseMap g)
  obtain ⟨αj, sqj⟩ := D'.exists_isPullback_mapAt_of_snd
    hi₀ (leOfHom j.hom.unop) _ hβjsnd
  have hstageProper : IsProper B S hS (pullback.snd ρ αj ≫
      D'.mapAt j.left.unop (leOfHom j.hom.unop)) := by
    refine (transfer (sys.siteDiagram.obj j) (yoneda.map (sys.siteDiagram.map g))
      (D'.targetAt j.left.unop (leOfHom j.hom.unop))
      ej _ hβj
      (D'.sourceAt j.left.unop (leOfHom j.hom.unop))
      (D'.mapAt j.left.unop (leOfHom j.hom.unop))
      ρ (yoneda.map w) αj hwe₀ sqj).mp ?_
    refine (isProper_pullback_snd_yoneda_map_iff B S hS w (sys.siteDiagram.map g)).mpr ?_
    exact (prop_overPullback_map_left_iff_pullback_snd
      (@_root_.AlgebraicGeometry.IsProper.{u} : MorphismProperty Scheme.{u})
      ((BigFppfOver.toScheme B S hS).map w) (sys.schemeDiagram.map g)).mp hstage
  exact universallyClosed_of_isSurjective_comp B S hS
    (isAlgebraicSpace_pullback B S hS ρ αj (isAlgebraicSpace_yoneda B S hS V)
      (D'.sourceAt_isAlgebraicSpace j.left.unop
        (leOfHom j.hom.unop))
      (D'.sourceAt_isAlgebraicSpace i₀ hi₀))
    (D'.sourceAt_isAlgebraicSpace j.left.unop
      (leOfHom j.hom.unop))
    (D'.targetAt_isAlgebraicSpace j.left.unop
      (leOfHom j.hom.unop)) _ _ hstageProper.2.2
    (surjective_pointsMap_of_isPullback B S hS (IsPullback.of_hasPullback ρ αj) hρs)

/-- If the system of bases is small for the site, the base change `f` of `f₀` to the limit is
proper and `f₀` is locally of finite type, then `f_i` is proper for some stage `i`. -/
theorem exists_isProper_mapAt (hb : IsSiteSmall B S hS D.base) (hf : IsProper B S hS D.mapLimit)
    (hf₀ : IsLocallyOfFiniteType B S hS D.map₀) :
    ∃ (i : I) (hi : D.initial ≤ i), IsProper B S hS (D.mapAt i hi) :=
  have := D.isCofiltered_op
  D.exists_isProper_mapAt_of_siteContainsBaseChangeLimits
    (IsSiteSmall.siteContainsBaseChangeLimits B S hS D.base hb) hf hf₀

end MorphismDescentSituation

end AlgebraicGeometry.Space

end
