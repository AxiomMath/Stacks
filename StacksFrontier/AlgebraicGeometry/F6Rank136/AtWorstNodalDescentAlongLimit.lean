module

public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.SyntomicDescentAlongLimit
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdealsDifferentials
public import StacksFrontier.AlgebraicGeometry.F6Rank136.AtWorstNodalRelativeDimensionOne
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties

/-!
# At-worst-nodal families of relative dimension one descend to a finite stage

Let a scheme be the limit of a cofiltered inverse system of schemes with affine transition
morphisms, and let `f₀ : X₀ ⟶ Y₀` be a morphism over one stage, with that stage and both of
`X₀`, `Y₀` quasi-compact and quasi-separated, and `f₀` locally of finite presentation. If the
base change of `f₀` to the limit is at-worst-nodal of relative dimension one, then so is its
base change to some later stage.

## Main results

* `AlgebraicGeometry.syntomicOfRelativeDimension_isStableUnderBaseChange`: being syntomic of
  relative dimension `d` is stable under base change.
* `AlgebraicGeometry.relativeSingularIdeal_comap_overPullback`: the relative singular subscheme
  of a base change is the inverse image of the relative singular subscheme.
* `AlgebraicGeometry.exists_syntomicOfRelativeDimension_baseChange_of_limitBaseChange`:
  syntomicity of a fixed relative dimension descends from the limit to a finite stage.
* `AlgebraicGeometry.exists_isAtWorstNodalOfRelativeDimensionOne_baseChange_of_limitBaseChange`:
  **Stacks Project, Tag 0C5F.**

## Implementation notes

Schemes over the chosen stage and their base changes are `CategoryTheory.Over` and
`CategoryTheory.Over.pullback`, as for the two descent statements this proof rests on; a
morphism `g : i ⟶ i₀` means that `i` is a later stage than `i₀`. The indexing category is taken
in the universe of the schemes, so that the filtered colimits of affine coordinate rings
underlying the limit are computed on underlying sets.

The two halves of the nodal condition descend separately. Syntomicity descends by
[Stacks, Tag 0C3L]; the local dimension of the fibre is locally constant on the source of a
syntomic morphism by [Stacks, Tag 02K1], so the locus where it equals `d` is open, it is
everything after base change to the limit because the local fibre dimension is a pointwise
invariant of a cartesian square ([Stacks, Tag 02FY]), and an open containing the image of the
limit already contains the image of a finite stage
(`AlgebraicGeometry.exists_map_eq_top`). That last step is applied to the system of base
changes of the later stages to the source of the syntomic stage, which is again a cofiltered
system with affine transition morphisms and compact objects; its limit cone comes from the
limit cone of the original system through `CategoryTheory.Limits.Over.conePost`.

For the unramifiedness half, the relative singular subscheme commutes with base change — this
is [Stacks, Tag 0C3I] at index one — so the base change of the inclusion of the relative
singular subscheme of `f₀` into `Y₀` is, up to a canonical isomorphism over the base change of
`Y₀`, the inclusion of the relative singular subscheme of the base change. Unramifiedness of
the latter therefore descends by [Stacks, Tag 0C4W]. A single later stage dominating the two
stages so obtained exists because the indexing category is cofiltered.

## References

* [Stacks Project, Tag 0C5F](https://stacks.math.columbia.edu/tag/0C5F)
* [Stacks Project, Tag 0C3I](https://stacks.math.columbia.edu/tag/0C3I)
* [Stacks Project, Tag 0C3L](https://stacks.math.columbia.edu/tag/0C3L)
* [Stacks Project, Tag 0C4W](https://stacks.math.columbia.edu/tag/0C4W)
* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
* [Stacks Project, Tag 02K1](https://stacks.math.columbia.edu/tag/02K1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Base change of the two halves of the nodal condition -/

/-- **Being syntomic of relative dimension `d` is stable under base change.** Syntomicity is,
and the local dimension of the fibre at a point is unchanged by base change. -/
public lemma syntomicOfRelativeDimension_isStableUnderBaseChange (d : ℕ) :
    MorphismProperty.IsStableUnderBaseChange
      (@SyntomicOfRelativeDimension d : MorphismProperty Scheme.{u}) := by
  constructor
  intro T S X Y g f a b hp hf
  have : LocallyOfFinitePresentation f := locallyOfFinitePresentation hf.1
  refine ⟨MorphismProperty.of_isPullback hp hf.1, fun x => ?_⟩
  rw [topologicalKrullDimAt_fiber_eq_of_isPullback hp x]
  exact hf.2 (a x)

/-- **The relative singular subscheme of a base change is the inverse image of the relative
singular subscheme.** It is cut out by the first Fitting ideal sheaf of the relative
differentials, and those commute with arbitrary base change. -/
public lemma relativeSingularIdeal_comap_overPullback {S T : Scheme.{u}} (h : T ⟶ S)
    (X Y : Over S) (f : X ⟶ Y) [LocallyOfFiniteType f.left] :
    (relativeSingularIdeal f.left).comap (pullback.fst X.hom h) =
      relativeSingularIdeal ((Over.pullback h).map f).left :=
  fittingIdeal_relativeDifferentials_comap _ _ _ _ (overPullback_isPullback h X Y f) 1

/-- For a quasi-coherent ideal sheaf on the source of a morphism of schemes over a base, a
property stable under isomorphism holds for the base change of the induced morphism out of the
closed subscheme exactly when it holds for the morphism out of the closed subscheme cut out by
the inverse-image ideal sheaf. -/
private lemma closedSubscheme_overPullback_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {S T : Scheme.{u}} (h : T ⟶ S) (X Y : Over S) (f : X ⟶ Y) (J : X.left.IdealSheafData) :
    P ((Over.pullback h).map (Over.homMk (J.subschemeι ≫ f.left) (by simp) :
        Over.mk (J.subschemeι ≫ X.hom) ⟶ Y)).left ↔
      P ((J.comap (pullback.fst X.hom h)).subschemeι ≫ ((Over.pullback h).map f).left) := by
  let a := pullback.fst X.hom h
  let m := (J.comapIso a).hom ≫ pullback.snd a J.subschemeι
  have hs : IsPullback (J.comap a).subschemeι m a J.subschemeι :=
    IsPullback.of_iso_pullback ⟨by simp [m]⟩ (J.comapIso a) (by simp) rfl
  let Z : Over S := Over.mk (J.subschemeι ≫ X.hom)
  let z : Z ⟶ Y := Over.homMk (J.subschemeι ≫ f.left) (by simp [Z])
  have hz := overPullback_isPullback h Z Y z
  have he : (hz.isoIsPullback _ _ (hs.flip.paste_vert (overPullback_isPullback h X Y f))).hom ≫
      ((J.comap a).subschemeι ≫ ((Over.pullback h).map f).left) =
      ((Over.pullback h).map z).left :=
    hz.isoIsPullback_hom_snd _ _ (hs.flip.paste_vert (overPullback_isPullback h X Y f))
  change P ((Over.pullback h).map z).left ↔ _
  rw [← he]
  exact P.cancel_left_of_respectsIso _ _

/-- Unramifiedness over the base passes between the base change of the inclusion of the
relative singular subscheme and the inclusion of the relative singular subscheme of the base
change. -/
private lemma unramified_relativeSingular_overPullback_iff {S T : Scheme.{u}} (h : T ⟶ S)
    (X Y : Over S) (f : X ⟶ Y) [LocallyOfFiniteType f.left] :
    Unramified ((Over.pullback h).map
        (Over.homMk ((relativeSingularIdeal f.left).subschemeι ≫ f.left) (by simp) :
          Over.mk ((relativeSingularIdeal f.left).subschemeι ≫ X.hom) ⟶ Y)).left ↔
      Unramified ((relativeSingularIdeal ((Over.pullback h).map f).left).subschemeι ≫
        ((Over.pullback h).map f).left) := by
  have : MorphismProperty.RespectsIso (@Unramified : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [← relativeSingularIdeal_comap_overPullback h X Y f]
  exact closedSubscheme_overPullback_iff (@Unramified) h X Y f _

/-! ### Descending syntomicity of a fixed relative dimension -/

/-- If the base change of a morphism over `S` along `h` is syntomic of relative dimension `d`,
then the local dimension of the fibre of the morphism at the image of every point of the base
change is `d`. -/
public lemma topologicalKrullDimAt_fiber_eq_of_overPullback {d : ℕ} {S T : Scheme.{u}}
    (h : T ⟶ S) {X Y : Over S} (f : X ⟶ Y) [LocallyOfFiniteType f.left]
    (hf : SyntomicOfRelativeDimension d ((Over.pullback h).map f).left)
    (x : ((Over.pullback h).obj X).left) :
    topologicalKrullDimAt (f.left.fiber (f.left (pullback.fst X.hom h x)))
      (f.left.asFiber (pullback.fst X.hom h x)) = (d : WithBot ℕ∞) :=
  (topologicalKrullDimAt_fiber_eq_of_isPullback (overPullback_isPullback h X Y f) x).symm.trans
    (hf.2 x)

/-- The second projection of `Y ×_S X` after the symmetry isomorphism is the first projection
of `X ×_S Y`, pointwise. -/
public lemma pullback_snd_pullbackSymmetry_hom_apply {X Y S : Scheme.{u}} (f : X ⟶ S)
    (g : Y ⟶ S) (x : (pullback f g : Scheme.{u})) :
    pullback.snd g f ((pullbackSymmetry f g).hom x) = pullback.fst f g x := by
  change ((pullbackSymmetry f g).hom ≫ pullback.snd g f) x = _
  rw [pullbackSymmetry_hom_comp_snd]

/-- The first projection of `Y ×_S X` after the symmetry isomorphism is the second projection
of `X ×_S Y`, pointwise. -/
public lemma pullback_fst_pullbackSymmetry_hom_apply {X Y S : Scheme.{u}} (f : X ⟶ S)
    (g : Y ⟶ S) (x : (pullback f g : Scheme.{u})) :
    pullback.fst g f ((pullbackSymmetry f g).hom x) = pullback.snd f g x := by
  change ((pullbackSymmetry f g).hom ≫ pullback.fst g f) x = _
  rw [pullbackSymmetry_hom_comp_fst]

/-- An open of a compact scheme over a stage of a cofiltered inverse system with affine
transition morphisms which contains the image of its base change to the limit already contains
the image of its base change to some later stage. -/
public lemma exists_forall_pullback_fst_mem_of_isLimit
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (i₁ : I)
    (X₁ : Over (D.obj i₁)) [IsCofiltered I] [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [CompactSpace (D.obj i₁)] [QuasiSeparatedSpace (D.obj i₁)]
    [CompactSpace X₁.left] [QuasiSeparatedSpace X₁.left] (hc : IsLimit c) (V : X₁.left.Opens)
    (hV : ∀ x, pullback.fst X₁.hom (c.π.app i₁) x ∈ V) :
    ∃ (i : I) (g : i ⟶ i₁), ∀ x, pullback.fst X₁.hom (D.map g) x ∈ V := by
  have : QuasiCompact X₁.hom := (quasiCompact_iff_compactSpace X₁.hom).mpr inferInstance
  let : MorphismProperty.IsStableUnderBaseChangeAlong (@QuasiCompact) X₁.hom :=
    ⟨fun pb hP => (inferInstance :
      MorphismProperty.IsStableUnderBaseChange (@QuasiCompact)).of_isPullback pb hP⟩
  let : MorphismProperty.IsStableUnderBaseChangeAlong (@IsAffineHom) X₁.hom :=
    ⟨fun pb hP => (inferInstance :
      MorphismProperty.IsStableUnderBaseChange (@IsAffineHom)).of_isPullback pb hP⟩
  -- the cofiltered system of base changes of the later stages to `X₁`, and its limit cone
  let H := Over.pullback X₁.hom ⋙ Over.forget X₁.left
  let DX := Over.post D ⋙ H
  let cX := H.mapCone ((Over.conePost D i₁).obj c)
  have (j : Over i₁) : CompactSpace (DX.obj j) := by
    dsimp [DX, H]
    exact (quasiCompact_iff_compactSpace (pullback.snd (D.map j.hom) X₁.hom)).mp
      (MorphismProperty.pullback_snd (P := @QuasiCompact) (D.map j.hom) X₁.hom inferInstance)
  have {j k : Over i₁} (g : j ⟶ k) : IsAffineHom (DX.map g) := by
    dsimp [DX, H]
    refine MorphismProperty.overPullbackMap (P := @IsAffineHom) X₁.hom ((Over.post D).map g) ?_
    change IsAffineHom (D.map g.left)
    infer_instance
  -- at the identity stage the system is `X₁` itself
  let idI : Over i₁ := Over.mk (𝟙 i₁)
  have : IsIso ((Over.post D).obj idI).hom := by
    rw [show ((Over.post D).obj idI).hom = 𝟙 (D.obj i₁) by simp [Over.post, idI]]
    exact IsIso.id _
  let eX₁ : DX.obj idI ≅ X₁.left := by
    dsimp [DX, H, idI]
    exact asIso (pullback.snd ((Over.post D).obj idI).hom X₁.hom)
  have hU : cX.π.app idI ⁻¹ᵁ (eX₁.hom ⁻¹ᵁ V) = ⊤ := by
    have hproj : cX.π.app idI ≫ eX₁.hom =
        pullback.snd ((Over.conePost D i₁).obj c).pt.hom X₁.hom :=
      ((Over.pullback X₁.hom).map (((Over.conePost D i₁).obj c).π.app idI)).w
    refine SetLike.ext fun x => iff_of_true ?_ trivial
    change (cX.π.app idI ≫ eX₁.hom) x ∈ V
    rw [hproj, ← pullback_fst_pullbackSymmetry_hom_apply]
    exact hV _
  obtain ⟨j, g, hj⟩ := exists_map_eq_top (I := Over i₁) DX cX
    (isLimitOfPreserves H (Over.isLimitConePost i₁ hc)) _ hU
  refine ⟨j.left, j.hom, fun x => ?_⟩
  let z : DX.obj j := (pullbackSymmetry X₁.hom (D.map j.hom)).hom x
  have hz : DX.map g z ∈ eX₁.hom ⁻¹ᵁ V := by
    change z ∈ DX.map g ⁻¹ᵁ (eX₁.hom ⁻¹ᵁ V)
    rw [hj]
    trivial
  have hproj : DX.map g ≫ eX₁.hom = pullback.snd (D.map j.hom) X₁.hom :=
    ((Over.pullback X₁.hom).map ((Over.post D).map g)).w
  change (DX.map g ≫ eX₁.hom) z ∈ V at hz
  rw [hproj] at hz
  exact pullback_snd_pullbackSymmetry_hom_apply X₁.hom (D.map j.hom) x ▸ hz

/-- **Syntomicity of relative dimension `d` descends to a finite stage.** If a locally finitely
presented morphism over a stage of a cofiltered inverse system with affine transition morphisms
becomes syntomic of relative dimension `d` over the limit, then it is already syntomic of
relative dimension `d` after base change to some later stage. -/
public lemma exists_syntomicOfRelativeDimension_baseChange_of_limitBaseChange (d : ℕ)
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (i₀ : I)
    (X₀ Y₀ : Over (D.obj i₀)) (f₀ : X₀ ⟶ Y₀) [IsCofiltered I]
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [CompactSpace (D.obj i₀)] [QuasiSeparatedSpace (D.obj i₀)]
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFinitePresentation f₀.left] (hc : IsLimit c)
    (hf : SyntomicOfRelativeDimension d ((Over.pullback (c.π.app i₀)).map f₀).left) :
    ∃ (i : I) (g : i ⟶ i₀),
      SyntomicOfRelativeDimension d ((Over.pullback (D.map g)).map f₀).left := by
  have hbc : MorphismProperty.IsStableUnderBaseChange
      (@SyntomicOfRelativeDimension d : MorphismProperty Scheme.{u}) :=
    syntomicOfRelativeDimension_isStableUnderBaseChange d
  obtain ⟨i₁, g₁, hsyn₁⟩ :=
    exists_syntomic_baseChange_of_syntomic_limitBaseChange D c i₀ X₀ Y₀ f₀ hc hf.1
  let X₁ : Over (D.obj i₁) := (Over.pullback (D.map g₁)).obj X₀
  let Y₁ : Over (D.obj i₁) := (Over.pullback (D.map g₁)).obj Y₀
  let f₁ : X₁ ⟶ Y₁ := (Over.pullback (D.map g₁)).map f₀
  have : LocallyOfFinitePresentation f₁.left := locallyOfFinitePresentation hsyn₁
  have : QuasiCompact X₀.hom := (quasiCompact_iff_compactSpace X₀.hom).mpr inferInstance
  let : MorphismProperty.IsStableUnderBaseChangeAlong (@IsAffineHom) X₀.hom :=
    ⟨fun pb hP => (inferInstance :
      MorphismProperty.IsStableUnderBaseChange (@IsAffineHom)).of_isPullback pb hP⟩
  have : CompactSpace (D.obj i₁) := QuasiCompact.compactSpace_of_compactSpace (D.map g₁)
  have : QuasiSeparatedSpace (D.obj i₁) := quasiSeparatedSpace_of_quasiSeparated (D.map g₁)
  have : IsAffineHom (pullback.fst X₀.hom (D.map g₁)) :=
    MorphismProperty.pullback_fst (P := @IsAffineHom) X₀.hom (D.map g₁) inferInstance
  have : IsSeparated (pullback.fst X₀.hom (D.map g₁)) := IsSeparated.of_isAffineHom _
  have : QuasiSeparatedSpace X₁.left :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst X₀.hom (D.map g₁))
  have : CompactSpace X₁.left := by
    dsimp [X₁]
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst X₀.hom (D.map g₁))
  -- the open locus where the local fibre dimension of `f₁` is `d`
  let V : X₁.left.Opens :=
    ⟨{x | topologicalKrullDimAt (f₁.left.fiber (f₁.left x)) (f₁.left.asFiber x) = d},
      (isLocallyConstant_fiberDimensionAt f₁.left hsyn₁).isOpen_fiber _⟩
  have hlim : SyntomicOfRelativeDimension d ((Over.pullback (c.π.app i₁)).map f₁).left :=
    (overPullback_map_comp_iff (@SyntomicOfRelativeDimension d) (D.map g₁) (c.π.app i₁) f₀).mp
      (by rwa [c.w g₁])
  obtain ⟨i, g, hg⟩ := exists_forall_pullback_fst_mem_of_isLimit D c i₁ X₁ hc V
    (topologicalKrullDimAt_fiber_eq_of_overPullback _ f₁ hlim)
  have hrel : SyntomicOfRelativeDimension d ((Over.pullback (D.map g)).map f₁).left := by
    refine ⟨MorphismProperty.overPullbackMap (P := @Syntomic) _ _ hsyn₁, fun x => ?_⟩
    rw [topologicalKrullDimAt_fiber_eq_of_isPullback
      (overPullback_isPullback (D.map g) X₁ Y₁ f₁) x]
    exact hg x
  refine ⟨i, g ≫ g₁, ?_⟩
  rw [D.map_comp]
  exact (overPullback_map_comp_iff (@SyntomicOfRelativeDimension d)
    (D.map g₁) (D.map g) f₀).mpr hrel

/-! ### Descending the nodal condition -/

/-- **Stacks Project, Tag 0C5F.** Let a scheme be the limit of a cofiltered inverse system of
schemes with affine transition morphisms, and let `f₀ : X₀ ⟶ Y₀` be a morphism locally of finite
presentation over a stage, with that stage and both of `X₀`, `Y₀` quasi-compact and
quasi-separated. If the base change of `f₀` to the limit is at-worst-nodal of relative dimension
one, then its base change to some later stage is at-worst-nodal of relative dimension one. -/
@[stacks 0C5F]
public theorem exists_isAtWorstNodalOfRelativeDimensionOne_baseChange_of_limitBaseChange
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (i₀ : I)
    (X₀ Y₀ : Over (D.obj i₀)) (f₀ : X₀ ⟶ Y₀) [IsCofiltered I]
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [CompactSpace (D.obj i₀)] [QuasiSeparatedSpace (D.obj i₀)]
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    (hf₀ : LocallyOfFinitePresentation f₀.left) (hc : IsLimit c)
    (hf : IsAtWorstNodalOfRelativeDimensionOne
      ((Over.pullback (c.π.app i₀)).map f₀).left) :
    ∃ (i : I) (g : i ⟶ i₀), IsAtWorstNodalOfRelativeDimensionOne
      ((Over.pullback (D.map g)).map f₀).left := by
  have hbc : MorphismProperty.IsStableUnderBaseChange
      (@SyntomicOfRelativeDimension 1 : MorphismProperty Scheme.{u}) :=
    syntomicOfRelativeDimension_isStableUnderBaseChange 1
  obtain ⟨i₁, g₁, hrel⟩ :=
    exists_syntomicOfRelativeDimension_baseChange_of_limitBaseChange 1 D c i₀ X₀ Y₀ f₀ hc hf.1
  -- the relative singular subscheme of `f₀`, as a scheme over the stage `i₀`
  let J := relativeSingularIdeal f₀.left
  let Z₀ : Over (D.obj i₀) := Over.mk (J.subschemeι ≫ X₀.hom)
  let z₀ : Z₀ ⟶ Y₀ := Over.homMk (J.subschemeι ≫ f₀.left) (by simp [Z₀])
  have : CompactSpace Z₀.left := QuasiCompact.compactSpace_of_compactSpace J.subschemeι
  have : QuasiSeparatedSpace Z₀.left := quasiSeparatedSpace_of_quasiSeparated J.subschemeι
  have : LocallyOfFiniteType z₀.left :=
    inferInstanceAs (LocallyOfFiniteType (J.subschemeι ≫ f₀.left))
  have : Unramified ((Over.pullback (c.π.app i₀)).map z₀).left :=
    (unramified_relativeSingular_overPullback_iff (c.π.app i₀) X₀ Y₀ f₀).mpr hf.2
  obtain ⟨i₂, g₂, hunr⟩ :=
    exists_unramified_baseChange_of_unramified_limitBaseChange D c i₀ Z₀ Y₀ z₀ hc
  obtain ⟨i, a, b, hab⟩ := IsCofiltered.cospan g₁ g₂
  refine ⟨i, a ≫ g₁, ?_, ?_⟩
  · rw [D.map_comp]
    exact (overPullback_map_comp_iff (@SyntomicOfRelativeDimension 1) (D.map g₁) (D.map a) f₀).mpr
      (MorphismProperty.overPullbackMap (P := @SyntomicOfRelativeDimension 1) _ _ hrel)
  · refine (unramified_relativeSingular_overPullback_iff (D.map (a ≫ g₁)) X₀ Y₀ f₀).mp ?_
    change Unramified ((Over.pullback (D.map (a ≫ g₁))).map z₀).left
    rw [hab, D.map_comp]
    exact (overPullback_map_comp_iff (@Unramified) (D.map g₂) (D.map b) z₀).mpr
      (MorphismProperty.overPullbackMap (P := @Unramified) _ _ hunr)

end AlgebraicGeometry

end
