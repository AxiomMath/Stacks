module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.AffineSpaceFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpaceProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ResidueFieldAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactAffineMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationLocalSchemeGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjQuadruplesFibreProduct

/-!
# An affine-space fibration over an integral space is a bundle over a dense open

In Situation 0EDT let `Y/B` be good and integral and let `f : X → Y` be a quasi-compact morphism
of good algebraic spaces over the base whose fibres over the spectra of the residue fields of `Y`
are affine `r`-spaces, `X_y ≅ 𝐀^r_{κ(y)}`. Then there is a nonempty open subscheme `V` of `Y`
over which `f` is the projection of affine `r`-space: `f^{-1}(V) ≅ 𝐀^r_V` over `V`.

## Main definitions

* `AlgebraicGeometry.Space.affineNhdsSystem`: the affine open neighbourhoods of a point of an
  object of the site, as a cofiltered system of objects of the site.
* `AlgebraicGeometry.Space.residueCone`: the cone of `Spec κ(t)` over that system.
* `AlgebraicGeometry.Space.affineSpaceMap`: affine `r`-space over a morphism of affine objects of
  the site.

## Main results

* `AlgebraicGeometry.Space.isLimitResidueCone`: `Spec κ(t)` is the limit of the affine open
  neighbourhoods of `t` when the local ring at `t` is a field.
* `AlgebraicGeometry.Space.isFinitePresentationColimit_residueCone`: Stacks 07SK for that limit.
* `AlgebraicGeometry.Space.exists_isOpenImmersion_isAffine_isIntegral`: an integral good space
  has an affine integral open chart.
* `AlgebraicGeometry.Space.exists_isPullback_isAffineSpaceBundle_of_isIntegralSpace`: over an
  integral base, an affine-space fibration is an affine-space bundle over a nonempty open.

## References

* [Stacks Project, Tag 0ERG](https://stacks.math.columbia.edu/tag/0ERG)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 0ENW](https://stacks.math.columbia.edu/tag/0ENW)
* [Stacks Project, Tag 01YX](https://stacks.math.columbia.edu/tag/01YX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The affine open neighbourhoods of a point of an object of the site -/

section Neighbourhoods

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T : BigFppfOver B S hS)
    (t : (BigFppfOver.toScheme B S hS).obj T)

/-- The morphism of schemes underlying the inclusion of two opens of an object of the site is
the inclusion of open subschemes. -/
theorem toScheme_map_opensObjectHomOfLE
    {V V' : ((BigFppfOver.toScheme B S hS).obj T).Opens} (h : V ≤ V') :
    (BigFppfOver.toScheme B S hS).map (GradedAlgebraRestriction.opensObjectHomOfLE T h) =
      ((BigFppfOver.toScheme B S hS).obj T).homOfLE h :=
  rfl

/-- A morphism of the site whose underlying morphism of schemes is an open immersion is an open
immersion after Yoneda. -/
private theorem isOpenImmersion_yoneda_map_of_isOpenImmersion_map {V W : BigFppfOver B S hS}
    {g : V ⟶ W} (hg : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map g)) :
    IsOpenImmersion B S hS (yoneda.map g) :=
  (presheaf_yoneda_map_iff B S hS (P := @AlgebraicGeometry.IsOpenImmersion.{u})
    inferInstance _).2 hg

/-- Restricting an open immersion `h_T → Y` to a Zariski open of `T` is an open immersion. -/
private theorem isOpenImmersion_yoneda_map_opensObjectι_comp
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : BigFppfOver B S hS) (U : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    {j : yoneda.obj T ⟶ Y} (hj : IsOpenImmersion B S hS j) :
    IsOpenImmersion B S hS (yoneda.map (opensObjectι B S hS T U) ≫ j) :=
  isOpenImmersion_comp B S hS _ _
    (isOpenImmersion_yoneda_map_of_isOpenImmersion_map B S hS
      (inferInstanceAs (AlgebraicGeometry.IsOpenImmersion U.ι))) hj

/-- The affine open neighbourhoods of a point `t` of an object `T` of the site, as a
cofiltered system of objects of the site, each an open subscheme of `T`. -/
def affineNhdsSystem : AffineOpenNhds ((BigFppfOver.toScheme B S hS).obj T) t ⥤
    BigFppfOver B S hS where
  obj W := opensObject B S hS T W.obj.1
  map f := GradedAlgebraRestriction.opensObjectHomOfLE T (leOfHom ((affineOpenNhds _ t).ι.map f))
  map_id W := BigFppfOver.map_toScheme_injective B S hS (by
    simp only [CategoryTheory.Functor.map_id, toScheme_map_opensObjectHomOfLE, Scheme.homOfLE_rfl]
    rfl)
  map_comp f g := BigFppfOver.map_toScheme_injective B S hS (by
    simp only [Functor.map_comp, toScheme_map_opensObjectHomOfLE]
    exact (Scheme.homOfLE_homOfLE _ _ _).symm)

/-- The morphism of schemes `Spec κ(t) ⟶ W` through which `Spec κ(t) ⟶ T` factors, for an open
neighbourhood `W` of `t`. -/
def residueFieldToOpen (W : AffineOpenNhds ((BigFppfOver.toScheme B S hS).obj T) t) :
    Spec (((BigFppfOver.toScheme B S hS).obj T).residueField t) ⟶
      Scheme.Opens.toScheme (X := (BigFppfOver.toScheme B S hS).obj T) W.obj.1 :=
  AlgebraicGeometry.IsOpenImmersion.lift
    (Scheme.Opens.ι (X := (BigFppfOver.toScheme B S hS).obj T) W.obj.1)
    (((BigFppfOver.toScheme B S hS).obj T).fromSpecResidueField t) (by
      intro z hz
      have hz' : z ∈ ({t} : Set ((BigFppfOver.toScheme B S hS).obj T)) :=
        (Scheme.range_fromSpecResidueField (X := (BigFppfOver.toScheme B S hS).obj T) t) ▸ hz
      rw [Set.mem_singleton_iff.1 hz']
      exact ⟨⟨t, W.obj.2⟩, rfl⟩)

/-- The factorisation `AlgebraicGeometry.Space.residueFieldToOpen` composed with the inclusion of
`W` is `Spec κ(t) ⟶ T`. -/
theorem residueFieldToOpen_ι (W : AffineOpenNhds ((BigFppfOver.toScheme B S hS).obj T) t) :
    residueFieldToOpen B S hS T t W ≫
        Scheme.Opens.ι (X := (BigFppfOver.toScheme B S hS).obj T) W.obj.1 =
      ((BigFppfOver.toScheme B S hS).obj T).fromSpecResidueField t :=
  AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _

/-- The point `t` lies on every affine open neighbourhood of it: the canonical morphism
`Spec κ(t) ⟶ T` factors through it. -/
def residueToAffineNhds (W : AffineOpenNhds ((BigFppfOver.toScheme B S hS).obj T) t) :
    (schemePointRepresentative B S hS T t).siteObject B S hS (yoneda.obj T) ⟶
      (affineNhdsSystem B S hS T t).obj W :=
  Over.homMk (ObjectProperty.homMk (residueFieldToOpen B S hS T t W)) (by
    apply ObjectProperty.hom_ext
    have h := congrArg (fun k => (B.inclusion.map k)) (Over.w
      (schemePointRepresentative B S hS T t).siteHom)
    simp only [Functor.map_comp] at h
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ B.inclusion.map T.hom) (residueFieldToOpen_ι B S hS T t W)).trans ?_
    rw [← toScheme_map_siteHom_schemePointRepresentative]
    exact h)

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.residueToAffineNhds` is the
factorisation of `Spec κ(t) ⟶ T` through the open subscheme. -/
theorem toScheme_map_residueToAffineNhds
    (W : AffineOpenNhds ((BigFppfOver.toScheme B S hS).obj T) t) :
    (BigFppfOver.toScheme B S hS).map (residueToAffineNhds B S hS T t W) =
      residueFieldToOpen B S hS T t W :=
  rfl

/-- The morphism `AlgebraicGeometry.Space.residueToAffineNhds` composed with the inclusion of the
open neighbourhood is the canonical morphism `Spec κ(t) ⟶ T`. -/
private theorem residueToAffineNhds_comp_opensObjectι
    (W : AffineOpenNhds ((BigFppfOver.toScheme B S hS).obj T) t) :
    residueToAffineNhds B S hS T t W ≫ opensObjectι B S hS T W.obj.1 =
      (schemePointRepresentative B S hS T t).siteHom :=
  BigFppfOver.map_toScheme_injective B S hS
    (((BigFppfOver.toScheme B S hS).map_comp _ _).trans
      ((congrArg₂ (· ≫ ·) (toScheme_map_residueToAffineNhds B S hS T t W)
          (toScheme_map_opensObjectι B S hS T W.obj.1)).trans
        ((residueFieldToOpen_ι B S hS T t W).trans
          (toScheme_map_siteHom_schemePointRepresentative B S hS T t).symm)))

/-- The morphisms `AlgebraicGeometry.Space.residueToAffineNhds` are compatible with the
transition maps of the system of affine open neighbourhoods. -/
theorem residueToAffineNhds_comp_map
    {W W' : AffineOpenNhds ((BigFppfOver.toScheme B S hS).obj T) t} (e : W ⟶ W') :
    residueToAffineNhds B S hS T t W ≫ (affineNhdsSystem B S hS T t).map e =
      residueToAffineNhds B S hS T t W' := by
  refine BigFppfOver.map_toScheme_injective B S hS ?_
  refine ((BigFppfOver.toScheme B S hS).map_comp _ _).trans ?_
  refine (cancel_mono (Scheme.Opens.ι (X := (BigFppfOver.toScheme B S hS).obj T) W'.obj.1)).1 ?_
  exact (Category.assoc _ _ _).trans ((congrArg _ (Scheme.homOfLE_ι _
    (leOfHom ((affineOpenNhds _ t).ι.map e)))).trans
    ((residueFieldToOpen_ι B S hS T t W).trans (residueFieldToOpen_ι B S hS T t W').symm))

/-- The cone of `Spec κ(t)` over the affine open neighbourhoods of `t`. -/
def residueCone : Cone (affineNhdsSystem B S hS T t) where
  pt := (schemePointRepresentative B S hS T t).siteObject B S hS (yoneda.obj T)
  π :=
    { app := residueToAffineNhds B S hS T t
      naturality := fun _ _ e => by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
        exact (residueToAffineNhds_comp_map B S hS T t e).symm }

/-- At a point whose local ring is a field, the canonical morphism `Spec κ(t) ⟶ Spec 𝒪_{T,t}` is
an isomorphism. -/
theorem isIso_spec_map_residue_of_isField {X : Scheme.{u}} (x : X)
    (hx : IsField (X.presheaf.stalk x)) : IsIso (Spec.map (X.residue x)) := by
  have hmax : IsLocalRing.maximalIdeal (X.presheaf.stalk x) = ⊥ :=
    IsLocalRing.isField_iff_maximalIdeal_eq.1 hx
  have hbij : Function.Bijective (IsLocalRing.residue (X.presheaf.stalk x)) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun a ha => ?_, IsLocalRing.residue_surjective⟩
    rwa [IsLocalRing.residue_eq_zero_iff, hmax] at ha
  have : IsIso (X.residue x) := (ConcreteCategory.isIso_iff_bijective _).2 hbij
  infer_instance

/-- When the local ring at `t` is a field, `Spec κ(t)` is the limit, in schemes, of the affine
open neighbourhoods of `t`. -/
def isLimitToSchemeResidueCone
    (ht : IsField (((BigFppfOver.toScheme B S hS).obj T).presheaf.stalk t)) :
    IsLimit ((BigFppfOver.toScheme B S hS).mapCone (residueCone B S hS T t)) := by
  haveI := isIso_spec_map_residue_of_isField t ht
  refine (isLimitSpecStalkCone ((BigFppfOver.toScheme B S hS).obj T) t).ofIsoLimit
    (Cone.ext (asIso (Spec.map (((BigFppfOver.toScheme B S hS).obj T).residue t))).symm
      fun W => ?_)
  exact (Iso.eq_inv_comp (asIso (Spec.map (((BigFppfOver.toScheme B S hS).obj T).residue t)))).2
    ((cancel_mono (Scheme.Opens.ι
    (X := (BigFppfOver.toScheme B S hS).obj T) W.obj.1)).1 (((Category.assoc _ _ _).trans
      (congrArg (Spec.map (((BigFppfOver.toScheme B S hS).obj T).residue t) ≫ ·)
        (Scheme.Opens.fromSpecStalkOfMem_ι _ _ _))).trans
      (residueFieldToOpen_ι B S hS T t W).symm))

/-- When the local ring at `t` is a field, `Spec κ(t)` is the limit, in the site, of the affine
open neighbourhoods of `t`. -/
def isLimitResidueCone (ht : IsField (((BigFppfOver.toScheme B S hS).obj T).presheaf.stalk t)) :
    IsLimit (residueCone B S hS T t) := by
  have : IsConnected (AffineOpenNhds ((BigFppfOver.toScheme B S hS).obj T) t) :=
    IsCofiltered.isConnected _
  exact isLimitOfReflects (BigFppfOver.toScheme B S hS) (isLimitToSchemeResidueCone B S hS T t ht)

/-- Stacks 07SK for the affine open neighbourhoods of `t`, when the local ring at `t` is a
field: base change exhibits the algebraic spaces of finite presentation over `Spec κ(t)` as the
filtered `2`-colimit of those over the affine open neighbourhoods of `t`. -/
theorem isFinitePresentationColimit_residueCone
    (ht : IsField (((BigFppfOver.toScheme B S hS).obj T).presheaf.stalk t)) :
    FinitePresentationSpacesOver.IsFinitePresentationColimit B S hS (affineNhdsSystem B S hS T t)
      ((schemePointRepresentative B S hS T t).siteObject B S hS (yoneda.obj T))
      (residueToAffineNhds B S hS T t) (residueToAffineNhds_comp_map B S hS T t) := by
  refine FinitePresentationSpacesOver.isFinitePresentationColimit_of_isLimit
    (isLimitOfPreserves yoneda (isLimitResidueCone B S hS T t ht)) B.contains_terminal
    (fun {W W'} e => ?_) (fun W => ?_) (fun W => ?_) ?_
    (Cardinal.one_lt_aleph0.trans B.aleph0_lt_cutoff) (fun W W' => ?_) ?_
  · exact FinitePresentationSpacesOver.isAffineHom_yoneda_map_of_isAffineHom B S hS _
      (inferInstanceAs (_root_.AlgebraicGeometry.IsAffineHom
        ((affineOpenNhdsDiagram ((BigFppfOver.toScheme B S hS).obj T) t).map e)))
  · exact isQuasiCompactSpace_yoneda_of_compactSpace B S hS _
      (inferInstanceAs (CompactSpace
        ((affineOpenNhdsDiagram ((BigFppfOver.toScheme B S hS).obj T) t).obj W)))
  · exact isAbsolutelyQuasiSeparated_yoneda_obj B S hS B.contains_terminal _
      (inferInstanceAs (QuasiSeparatedSpace
        ((affineOpenNhdsDiagram ((BigFppfOver.toScheme B S hS).obj T) t).obj W)))
  · refine (Cardinal.mk_le_of_injective (f := fun W : AffineOpenNhds
        ((BigFppfOver.toScheme B S hS).obj T) t =>
      (⟨W.obj.1, W.property⟩ : ((BigFppfOver.toScheme B S hS).obj T).affineOpens))
      fun W W' h => ?_).trans_lt
      (((BigFppfOver.toScheme B S hS).obj T).mk_affineOpens_le_size.trans_lt T.left.property)
    obtain ⟨⟨V, hV⟩, hA⟩ := W
    obtain ⟨⟨V', hV'⟩, hA'⟩ := W'
    obtain rfl : V = V' := congrArg Subtype.val h
    rfl
  · exact Cardinal.le_one_iff_subsingleton.2
      ⟨fun f g => (affineOpenNhds _ t).ι.map_injective (Subsingleton.elim _ _)⟩
  · refine Space.baseChangeSizeBounded_of_mono B S hS _ fun {W W'} e => ?_
    have : Mono ((affineNhdsSystem B S hS T t).map e) := by
      have hoi : AlgebraicGeometry.IsOpenImmersion
          ((BigFppfOver.toScheme B S hS).map ((affineNhdsSystem B S hS T t).map e)) := by
        show AlgebraicGeometry.IsOpenImmersion (Scheme.homOfLE _
          (leOfHom ((affineOpenNhds _ t).ι.map e)))
        infer_instance
      have hm : Mono ((BigFppfOver.toScheme B S hS).map ((affineNhdsSystem B S hS T t).map e)) :=
        AlgebraicGeometry.IsOpenImmersion.mono _
      exact (BigFppfOver.toScheme B S hS).mono_of_mono_map hm
    exact Functor.map_mono yoneda ((affineNhdsSystem B S hS T t).map e)

end Neighbourhoods

/-! ### An affine integral open chart of an integral good space -/

section Chart

variable (D : BaseSpaceDimensionSituation.{u})
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- An integral good algebraic space `Y` has an affine integral open chart: an object `T` of the
site, affine and integral, with an open immersion `h_T → Y`. -/
theorem exists_isOpenImmersion_isAffine_isIntegral (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hint : IsIntegralSpace D.site D.base D.base_mem Y) :
    ∃ (T : BigFppfOver D.site D.base D.base_mem) (j : yoneda.obj T ⟶ Y),
      IsOpenImmersion D.site D.base D.base_mem j ∧
        IsAffine ((BigFppfOver.toScheme D.site D.base D.base_mem).obj T) ∧
          IsIntegral ((BigFppfOver.toScheme D.site D.base D.base_mem).obj T) := by
  obtain ⟨G, hG, hrep, hdense⟩ :=
    D.exists_denseRange_isRepresentable_isOpenSubspace_of_isGood sY hY
  have := hint.2.2
  set U₀ := G.toFunctor.reprX
  set j₀ : yoneda.obj U₀ ⟶ Y := G.toFunctor.reprW.hom ≫ G.ι
  have hj₀ : IsOpenImmersion D.site D.base D.base_mem j₀ :=
    isOpenImmersion_comp D.site D.base D.base_mem _ _
      (isOpenImmersion_of_isIso D.site D.base D.base_mem _) hG.2
  obtain ⟨y₀⟩ := (inferInstance : Nonempty (points D.site D.base D.base_mem Y))
  obtain ⟨g₀⟩ := hdense.nonempty_iff.2 ⟨y₀⟩
  set u₀ := schemePointsHomeomorph D.site D.base D.base_mem U₀
    (pointsMap D.site D.base D.base_mem _ G.toFunctor.reprW.inv g₀)
  obtain ⟨-, ⟨W₀, hW₀, rfl⟩, hu₀, -⟩ :=
    ((BigFppfOver.toScheme D.site D.base D.base_mem).obj
      U₀).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ u₀) isOpen_univ
  set T := opensObject D.site D.base D.base_mem U₀ W₀
  set j := yoneda.map (opensObjectι D.site D.base D.base_mem U₀ W₀) ≫ j₀
  have hj : IsOpenImmersion D.site D.base D.base_mem j :=
    isOpenImmersion_yoneda_map_opensObjectι_comp D.site D.base D.base_mem U₀ W₀ hj₀
  refine ⟨T, j, hj, hW₀, ?_⟩
  have hTsp := isAlgebraicSpace_yoneda D.site D.base D.base_mem T
  have hred : IsReduced ((BigFppfOver.toScheme D.site D.base D.base_mem).obj T) :=
    (exists_atlas_iff_of_representable D.site D.base D.base_mem (yoneda.obj T)
      (fun Z : Scheme.{u} => IsReduced Z) T (Iso.refl _)).1
      (hasEtaleLocalProperty_of_isEtale D.site D.base D.base_mem hTsp hY.1
        (isEtale_of_isOpenImmersion D.site D.base D.base_mem hj) hint.1)
  have hemb := isOpenEmbedding_pointsMap_of_isOpenImmersion D hY.1 hj
  have hne : (Set.univ ∩ Set.range (pointsMap D.site D.base D.base_mem _ j)).Nonempty :=
    ⟨_, Set.mem_univ _, (schemePointsHomeomorph D.site D.base D.base_mem T).symm ⟨u₀, hu₀⟩, rfl⟩
  have hirr : IsIrreducible (Set.univ : Set (points D.site D.base D.base_mem (yoneda.obj T))) := by
    simpa using isIrreducible_preimage_of_isOpenEmbedding hemb
      (IrreducibleSpace.isIrreducible_univ _) hne
  have : IrreducibleSpace (points D.site D.base D.base_mem (yoneda.obj T)) :=
    (irreducibleSpace_def _).2 hirr
  have : IrreducibleSpace ((BigFppfOver.toScheme D.site D.base D.base_mem).obj T) :=
    (schemePointsHomeomorph D.site D.base D.base_mem T).irreducibleSpace_iff.1 inferInstance
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end Chart

/-! ### Finite presentation -/

section FinitePresentation

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- A quasi-compact morphism of good algebraic spaces over the base is of finite presentation. -/
theorem isFinitePresentation_of_isQuasiCompact (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y) (hbase : f ≫ sY = sX)
    (hqc : IsQuasiCompact D.site D.base D.base_mem f) :
    IsFinitePresentation D.site D.base D.base_mem f :=
  ⟨isLocallyOfFinitePresentation_of_isLocallyOfFiniteType D.site D.base D.base_mem hX.1 hY.1 f
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)
      (isLocallyOfFiniteType_of_comp D.site D.base D.base_mem hX.1 hY.1 D.isAlgebraicSpace f sY
        (by rw [hbase]; exact hX.2.2)),
    hqc, isQuasiSeparated_of_comp D.site D.base D.base_mem f sY (by rw [hbase]; exact hX.2.1)⟩

/-- The projection of a represented affine space over an affine object of the site is of finite
presentation. -/
theorem isFinitePresentation_yoneda_map_affineSpaceProj (r : ℕ)
    (V : BigFppfOver D.site D.base D.base_mem)
    (hV : IsAffine ((BigFppfOver.toScheme D.site D.base D.base_mem).obj V)) :
    IsFinitePresentation D.site D.base D.base_mem
      (yoneda.map (BigFppfOver.affineSpaceProj D.site D.base D.base_mem r V hV)) :=
  ⟨(holdsOnEveryEtaleChart_yoneda_map_iff D.site D.base D.base_mem
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget _).2
      (inferInstanceAs (LocallyOfFinitePresentation (𝔸(ULift.{u} (Fin r);
        (BigFppfOver.toScheme D.site D.base D.base_mem).obj V) ↘ _))),
    isQuasiCompact_yoneda_map_of_isAffineHom D.site D.base D.base_mem _
      (inferInstanceAs (_root_.AlgebraicGeometry.IsAffineHom (𝔸(ULift.{u} (Fin r);
        (BigFppfOver.toScheme D.site D.base D.base_mem).obj V) ↘ _))),
    (isQuasiSeparated_yoneda_map_iff D.site D.base D.base_mem _).2
      (inferInstanceAs (QuasiSeparated (𝔸(ULift.{u} (Fin r);
        (BigFppfOver.toScheme D.site D.base D.base_mem).obj V) ↘ _)))⟩

end FinitePresentation

/-! ### Affine spaces over objects of the site -/

section AffineSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of the site whose underlying morphism of schemes is an isomorphism is an
isomorphism. -/
theorem isIso_of_isIso_toScheme_map {V W : BigFppfOver B S hS} (g : V ⟶ W)
    (hg : IsIso ((BigFppfOver.toScheme B S hS).map g)) : IsIso g :=
  isIso_of_reflects_iso g (BigFppfOver.toScheme B S hS)

/-- A pullback square of presheaves with a represented left edge `h_b` stays a pullback square
after replacing `b` by `b ≫ g⁻¹` and the bottom edge `k` by `h_g ≫ k`, for an isomorphism `g`. -/
private theorem isPullback_yoneda_map_comp_inv {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Tf P R : BigFppfOver B S hS} {a : yoneda.obj Tf ⟶ X} {b : Tf ⟶ P} {f : X ⟶ Y}
    {k : yoneda.obj P ⟶ Y} (hpb : IsPullback a (yoneda.map b) f k) (g : R ⟶ P) [IsIso g]
    {m : yoneda.obj R ⟶ Y} (hm : m = yoneda.map g ≫ k) :
    IsPullback a (yoneda.map (b ≫ inv g)) f m :=
  hpb.of_iso (Iso.refl _) (Iso.refl _) (yoneda.mapIso (asIso g).symm) (Iso.refl _)
    (by simp) (by simp [Functor.map_comp]) (by simp) (by
      simp only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom, Iso.symm_hom, asIso_inv,
        hm, Functor.map_inv, IsIso.inv_hom_id_assoc])

/-- Affine space over a morphism of affine objects of the site: the morphism
`𝐀^r_V ⟶ 𝐀^r_W` over `φ : V ⟶ W`, as a morphism of the site. -/
def affineSpaceMap (r : ℕ) {V W : BigFppfOver B S hS} (φ : V ⟶ W)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W)) :
    BigFppfOver.affineSpace B S hS r V hV ⟶ BigFppfOver.affineSpace B S hS r W hW :=
  BigFppfOver.homMk B S hS _ _ (AffineSpace.map (ULift.{u} (Fin r))
    ((BigFppfOver.toScheme B S hS).map φ)) (by
      have h1 : (BigFppfOver.toScheme B S hS).map φ ≫ B.inclusion.map W.hom =
          B.inclusion.map V.hom :=
        (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map (Over.w φ))
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ B.inclusion.map W.hom) (AffineSpace.map_over (n := ULift.{u} (Fin r))
          ((BigFppfOver.toScheme B S hS).map φ))).trans
          ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h1))))

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.affineSpaceMap` is the induced
morphism of affine spaces. -/
theorem toScheme_map_affineSpaceMap (r : ℕ) {V W : BigFppfOver B S hS} (φ : V ⟶ W)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W)) :
    (BigFppfOver.toScheme B S hS).map (affineSpaceMap B S hS r φ hV hW) =
      AffineSpace.map (ULift.{u} (Fin r)) ((BigFppfOver.toScheme B S hS).map φ) :=
  rfl

/-- Affine space over a morphism of affine objects of the site is cartesian over that morphism. -/
theorem isPullback_affineSpaceMap (r : ℕ) {V W : BigFppfOver B S hS} (φ : V ⟶ W)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W)) :
    IsPullback (affineSpaceMap B S hS r φ hV hW) (BigFppfOver.affineSpaceProj B S hS r V hV)
      (BigFppfOver.affineSpaceProj B S hS r W hW) φ :=
  IsPullback.of_map (BigFppfOver.toScheme B S hS)
    (BigFppfOver.map_toScheme_injective B S hS
      (((BigFppfOver.toScheme B S hS).map_comp (affineSpaceMap B S hS r φ hV hW)
          (BigFppfOver.affineSpaceProj B S hS r W hW)).trans
        ((AffineSpace.map_over (n := ULift.{u} (Fin r)) ((BigFppfOver.toScheme B S hS).map φ)).trans
          ((BigFppfOver.toScheme B S hS).map_comp (BigFppfOver.affineSpaceProj B S hS r V hV)
            φ).symm)))
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin r)) ((BigFppfOver.toScheme B S hS).map φ))

/-- An object `Tf` of the site whose scheme is affine `r`-space over `Q`, by an isomorphism over
`b : Tf ⟶ Q`, is the pullback of affine `r`-space over an affine `V` along any `φ : P ⟶ V`, for
`P ≅ Q`. -/
private theorem exists_isPullback_affineSpaceProj_of_iso (r : ℕ)
    {Tf Q P V : BigFppfOver B S hS}
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) (b : Tf ⟶ Q) (g : P ⟶ Q) [IsIso g]
    (φ : P ⟶ V)
    (e : (BigFppfOver.toScheme B S hS).obj Tf ≅
      𝔸(ULift.{u} (Fin r); (BigFppfOver.toScheme B S hS).obj Q))
    (he : e.hom ≫ 𝔸(ULift.{u} (Fin r); (BigFppfOver.toScheme B S hS).obj Q) ↘
        (BigFppfOver.toScheme B S hS).obj Q = (BigFppfOver.toScheme B S hS).map b) :
    ∃ ψ : Tf ⟶ BigFppfOver.affineSpace B S hS r V hV,
      IsPullback ψ (b ≫ inv g) (BigFppfOver.affineSpaceProj B S hS r V hV) φ := by
  obtain ⟨ψs, hψsdef⟩ : ∃ ψs : (BigFppfOver.toScheme B S hS).obj Tf ⟶
      𝔸(ULift.{u} (Fin r); (BigFppfOver.toScheme B S hS).obj V),
      ψs = e.hom ≫ AffineSpace.map (ULift.{u} (Fin r))
        ((BigFppfOver.toScheme B S hS).map (inv g ≫ φ)) :=
    ⟨_, rfl⟩
  have hψs₁ : ψs ≫ 𝔸(ULift.{u} (Fin r); (BigFppfOver.toScheme B S hS).obj V) ↘ _ =
      (BigFppfOver.toScheme B S hS).map (b ≫ inv g ≫ φ) := by
    rw [hψsdef, Category.assoc, AffineSpace.map_over, ← Category.assoc, he,
      ← Functor.map_comp]
  have hψsq : IsPullback ψs ((BigFppfOver.toScheme B S hS).map (b ≫ inv g))
      (𝔸(ULift.{u} (Fin r); (BigFppfOver.toScheme B S hS).obj V) ↘ _)
      ((BigFppfOver.toScheme B S hS).map φ) := by
    refine (AffineSpace.isPullback_map (n := ULift.{u} (Fin r))
      ((BigFppfOver.toScheme B S hS).map (inv g ≫ φ))).of_iso e.symm (Iso.refl _)
      ((BigFppfOver.toScheme B S hS).mapIso (asIso g)).symm (Iso.refl _)
      ?_ ?_ ?_ ?_
    · simp [hψsdef]
    · simp only [Iso.symm_hom, Functor.mapIso_inv, asIso_inv, Functor.map_comp]
      rw [← he]
      simp
    · simp
    · simp
  let ψ : Tf ⟶ BigFppfOver.affineSpace B S hS r V hV :=
    Over.homMk (ObjectProperty.homMk ψs) (ObjectProperty.hom_ext _
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ B.inclusion.map V.hom) hψs₁).trans
        ((B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map
          (Over.w (b ≫ inv g ≫ φ)))))))
  exact ⟨ψ, IsPullback.of_map (BigFppfOver.toScheme B S hS)
    (BigFppfOver.map_toScheme_injective B S hS
      ((((BigFppfOver.toScheme B S hS).map_comp ψ
        (BigFppfOver.affineSpaceProj B S hS r V hV)).trans hψsq.w).trans
        ((BigFppfOver.toScheme B S hS).map_comp (b ≫ inv g) φ).symm)) hψsq⟩

end AffineSpace

/-! ### The two spaces of finite presentation over a chart -/

section Objects

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The base change `X ×_Y h_V → h_V` of a quasi-compact morphism of good spaces along a
morphism `h_V → Y` from an object of the site, as an algebraic space of finite presentation
over `V`. -/
def baseChangeFinitePresentation (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (f : X ⟶ Y) (hbase : f ≫ sY = sX)
    (hqc : IsQuasiCompact D.site D.base D.base_mem f) {V : BigFppfOver D.site D.base D.base_mem}
    (j₀ : yoneda.obj V ⟶ Y) : FinitePresentationSpacesOver D.site D.base D.base_mem V :=
  ⟨Over.mk (pullback.snd f j₀),
    isAlgebraicSpace_pullback D.site D.base D.base_mem f j₀ hX.1
      (isAlgebraicSpace_yoneda D.site D.base D.base_mem V) hY.1,
    isFinitePresentation_of_isPullback D.site D.base D.base_mem
      (isAlgebraicSpace_pullback D.site D.base D.base_mem f j₀ hX.1
        (isAlgebraicSpace_yoneda D.site D.base D.base_mem V) hY.1) hX.1
      (isAlgebraicSpace_yoneda D.site D.base D.base_mem V) hY.1
      (IsPullback.of_hasPullback f j₀)
      (isFinitePresentation_of_isQuasiCompact D sX hX sY hY f hbase hqc)⟩

/-- Affine `r`-space over an affine object `V` of the site, as an algebraic space of finite
presentation over `V`. -/
def affineSpaceFinitePresentation (r : ℕ) (V : BigFppfOver D.site D.base D.base_mem)
    (hV : IsAffine ((BigFppfOver.toScheme D.site D.base D.base_mem).obj V)) :
    FinitePresentationSpacesOver D.site D.base D.base_mem V :=
  ⟨Over.mk (yoneda.map (BigFppfOver.affineSpaceProj D.site D.base D.base_mem r V hV)),
    isAlgebraicSpace_yoneda _ _ _ _, isFinitePresentation_yoneda_map_affineSpaceProj D r V hV⟩

end Objects

/-! ### Spreading out the generic fibre -/

section SpreadOut

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- If the base change of `f` along `h_P → h_V → Y` and affine `r`-space over `V` pulled back to
`P` are both identified with the same object `Tf` of the site, then the base changes to `P` of
`X ×_Y h_V` and of `h_{𝐀^r_V}` are isomorphic. -/
private theorem nonempty_baseChange_iso_affineSpaceFinitePresentation (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y) (hbase : f ≫ sY = sX)
    (r : ℕ) (hqc : IsQuasiCompact D.site D.base D.base_mem f)
    {Tf P V : BigFppfOver D.site D.base D.base_mem}
    (hV : IsAffine ((BigFppfOver.toScheme D.site D.base D.base_mem).obj V)) (p : P ⟶ V)
    (j₀ : yoneda.obj V ⟶ Y) {a : yoneda.obj Tf ⟶ X} {b : Tf ⟶ P}
    (hpb : IsPullback a (yoneda.map b) f (yoneda.map p ≫ j₀))
    {ψ : Tf ⟶ BigFppfOver.affineSpace D.site D.base D.base_mem r V hV}
    (hψ : IsPullback ψ b (BigFppfOver.affineSpaceProj D.site D.base D.base_mem r V hV) p) :
    Nonempty ((FinitePresentationSpacesOver.baseChange D.site D.base D.base_mem p).obj
        (baseChangeFinitePresentation D sX hX sY hY f hbase hqc j₀) ≅
      (FinitePresentationSpacesOver.baseChange D.site D.base D.base_mem p).obj
        (affineSpaceFinitePresentation D r V hV)) := by
  have hLX := (IsPullback.of_hasPullback (pullback.snd f j₀) (yoneda.map p)).paste_horiz
    (IsPullback.of_hasPullback f j₀)
  have hLA := IsPullback.of_hasPullback
    (yoneda.map (BigFppfOver.affineSpaceProj D.site D.base D.base_mem r V hV)) (yoneda.map p)
  set isoX := hLX.isoIsPullback _ _ hpb
  set isoA := (hψ.map yoneda).isoIsPullback _ _ hLA
  have hθ : (isoX ≪≫ isoA).hom ≫ pullback.snd _ _ = pullback.snd _ _ := by
    rw [Iso.trans_hom, Category.assoc, IsPullback.isoIsPullback_hom_snd,
      IsPullback.isoIsPullback_hom_snd]
  exact ⟨(ObjectProperty.fullyFaithfulι _).preimageIso (Over.isoMk (isoX ≪≫ isoA) hθ)⟩

/-- If the base changes along `e' : W ⟶ V` of `X ×_Y h_V` and of `h_{𝐀^r_V}` are isomorphic, for
affine `V` and `W`, then `h_{𝐀^r_W} → h_W` is cartesian over `f` along `h_W → h_V → Y`. -/
private theorem exists_isPullback_affineSpaceProj_of_baseChange_iso (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y) (hbase : f ≫ sY = sX)
    (r : ℕ) (hqc : IsQuasiCompact D.site D.base D.base_mem f)
    {V W : BigFppfOver D.site D.base D.base_mem}
    (hV : IsAffine ((BigFppfOver.toScheme D.site D.base D.base_mem).obj V))
    (hW : IsAffine ((BigFppfOver.toScheme D.site D.base D.base_mem).obj W)) (e' : W ⟶ V)
    (j₀ : yoneda.obj V ⟶ Y)
    (Θ' : (FinitePresentationSpacesOver.baseChange D.site D.base D.base_mem e').obj
        (baseChangeFinitePresentation D sX hX sY hY f hbase hqc j₀) ≅
      (FinitePresentationSpacesOver.baseChange D.site D.base D.base_mem e').obj
        (affineSpaceFinitePresentation D r V hV)) :
    ∃ jX : yoneda.obj (BigFppfOver.affineSpace D.site D.base D.base_mem r W hW) ⟶ X,
      IsPullback jX (yoneda.map (BigFppfOver.affineSpaceProj D.site D.base D.base_mem r W hW)) f
        (yoneda.map e' ≫ j₀) := by
  have hAsq := (isPullback_affineSpaceMap D.site D.base D.base_mem r e' hW hV).map yoneda
  obtain ⟨isoL, hisoL⟩ : ∃ isoL : yoneda.obj (BigFppfOver.affineSpace D.site D.base D.base_mem r W
      hW) ≅ pullback (pullback.snd f j₀) (yoneda.map e'),
      isoL.hom ≫ pullback.snd _ _ =
        yoneda.map (BigFppfOver.affineSpaceProj D.site D.base D.base_mem r W hW) :=
    ⟨hAsq.isoIsPullback _ _ (IsPullback.of_hasPullback _ _) ≪≫
      (ObjectProperty.ι _ ⋙ Over.forget _).mapIso Θ'.symm,
      (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Over.w Θ'.inv.hom)).trans
        (IsPullback.isoIsPullback_hom_snd _ _ _ _))⟩
  refine ⟨isoL.hom ≫ pullback.fst _ _ ≫ pullback.fst f j₀,
    ((IsPullback.of_hasPullback (pullback.snd f j₀) (yoneda.map e')).paste_horiz
      (IsPullback.of_hasPullback f j₀)).of_iso isoL.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) ?_ (by simp) (by simp)⟩
  rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, ← hisoL, Iso.inv_hom_id_assoc]

/-- If the base changes along an inclusion `e' : W ⟶ V` of affine open neighbourhoods of `t` of
`X ×_Y h_V` and of `h_{𝐀^r_V}` are isomorphic, for an open immersion `h_V → Y`, then over the
nonempty open `h_W → Y` the morphism `f` is the projection of affine `r`-space. -/
private theorem exists_isPullback_isAffineSpaceBundle_of_baseChange_iso
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ)
    (hqc : IsQuasiCompact D.site D.base D.base_mem f) {T : BigFppfOver D.site D.base D.base_mem}
    (t : (BigFppfOver.toScheme D.site D.base D.base_mem).obj T)
    {i jj : AffineOpenNhds ((BigFppfOver.toScheme D.site D.base D.base_mem).obj T) t}
    (hV : IsAffine ((BigFppfOver.toScheme D.site D.base D.base_mem).obj
      ((affineNhdsSystem D.site D.base D.base_mem T t).obj i))) (e' : jj ⟶ i)
    (j₀ : yoneda.obj ((affineNhdsSystem D.site D.base D.base_mem T t).obj i) ⟶ Y)
    (hj₀ : IsOpenImmersion D.site D.base D.base_mem j₀)
    (Θ' : (FinitePresentationSpacesOver.baseChange D.site D.base D.base_mem
        ((affineNhdsSystem D.site D.base D.base_mem T t).map e')).obj
        (baseChangeFinitePresentation D sX hX sY hY f hbase hqc j₀) ≅
      (FinitePresentationSpacesOver.baseChange D.site D.base D.base_mem
        ((affineNhdsSystem D.site D.base D.base_mem T t).map e')).obj
        (affineSpaceFinitePresentation D r _ hV)) :
    ∃ (V A : BigFppfOver D.site D.base D.base_mem) (jY : yoneda.obj V ⟶ Y)
      (jX : yoneda.obj A ⟶ X) (g : A ⟶ V),
      IsOpenImmersion D.site D.base D.base_mem jY ∧
        (Set.range (pointsMap D.site D.base D.base_mem _ jY)).Nonempty ∧
        IsPullback jX (yoneda.map g) f jY ∧
        ∃ (_ : LocallyOfFiniteType ((BigFppfOver.toScheme D.site D.base D.base_mem).map g)),
        Flat ((BigFppfOver.toScheme D.site D.base D.base_mem).map g) ∧
        AlgebraicGeometry.RelativeDimension
          ((BigFppfOver.toScheme D.site D.base D.base_mem).map g) r ∧
        Stacks.Chow.IsAffineSpaceBundle
          ((BigFppfOver.toScheme D.site D.base D.base_mem).map g) r := by
  have hVaff : IsAffine ((BigFppfOver.toScheme D.site D.base D.base_mem).obj
      ((affineNhdsSystem D.site D.base D.base_mem T t).obj jj)) := jj.property
  obtain ⟨jX, hjX⟩ := exists_isPullback_affineSpaceProj_of_baseChange_iso D sX hX sY hY f hbase r
    hqc hV hVaff ((affineNhdsSystem D.site D.base D.base_mem T t).map e') j₀ Θ'
  have hιe : IsOpenImmersion D.site D.base D.base_mem
      (yoneda.map ((affineNhdsSystem D.site D.base D.base_mem T t).map e')) :=
    isOpenImmersion_yoneda_map_of_isOpenImmersion_map D.site D.base D.base_mem
      (inferInstanceAs (AlgebraicGeometry.IsOpenImmersion
        (Scheme.homOfLE ((BigFppfOver.toScheme D.site D.base D.base_mem).obj T)
          (leOfHom ((affineOpenNhds _ t).ι.map e')))))
  exact ⟨(affineNhdsSystem D.site D.base D.base_mem T t).obj jj,
    BigFppfOver.affineSpace D.site D.base D.base_mem r _ hVaff,
    yoneda.map ((affineNhdsSystem D.site D.base D.base_mem T t).map e') ≫ j₀, jX,
    BigFppfOver.affineSpaceProj D.site D.base D.base_mem r _ hVaff,
    isOpenImmersion_comp D.site D.base D.base_mem _ _ hιe hj₀,
    ⟨_, Set.mem_range_self ((schemePointsHomeomorph D.site D.base D.base_mem
      ((affineNhdsSystem D.site D.base D.base_mem T t).obj jj)).symm ⟨t, jj.obj.2⟩)⟩,
    hjX, inferInstanceAs (LocallyOfFiniteType (𝔸(ULift.{u} (Fin r);
      (BigFppfOver.toScheme D.site D.base D.base_mem).obj
        ((affineNhdsSystem D.site D.base D.base_mem T t).obj jj)) ↘ _)),
    Stacks.Chow.flat_affineSpaceOver _ r, Stacks.Chow.relativeDimension_affineSpaceOver _ r,
    Stacks.Chow.isAffineSpaceBundle_affineSpaceOver _ r⟩

/-- An affine-space fibration over an integral space is a bundle over a nonempty open. In
Situation 0EDT let `Y/B` be good and integral and let `f : X → Y` be a quasi-compact morphism of
good spaces with `X_y ≅ 𝐀^r_{κ(y)}` for every `y`. Then there are a nonempty open immersion
`h_V → Y` from an affine scheme `V` of the site and a cartesian square
`h_{𝐀^r_V} → X` over `h_V → Y`: over `V`, `f` is the projection of affine `r`-space. -/
theorem exists_isPullback_isAffineSpaceBundle_of_isIntegralSpace
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ)
    (hqc : IsQuasiCompact D.site D.base D.base_mem f) (hfib : HasAffineSpaceFibres D sY hY f r)
    (hint : IsIntegralSpace D.site D.base D.base_mem Y) :
    ∃ (V A : BigFppfOver D.site D.base D.base_mem) (jY : yoneda.obj V ⟶ Y)
      (jX : yoneda.obj A ⟶ X) (g : A ⟶ V),
      IsOpenImmersion D.site D.base D.base_mem jY ∧
        (Set.range (pointsMap D.site D.base D.base_mem _ jY)).Nonempty ∧
        IsPullback jX (yoneda.map g) f jY ∧
        ∃ (_ : LocallyOfFiniteType ((BigFppfOver.toScheme D.site D.base D.base_mem).map g)),
        Flat ((BigFppfOver.toScheme D.site D.base D.base_mem).map g) ∧
        AlgebraicGeometry.RelativeDimension
          ((BigFppfOver.toScheme D.site D.base D.base_mem).map g) r ∧
        Stacks.Chow.IsAffineSpaceBundle
          ((BigFppfOver.toScheme D.site D.base D.base_mem).map g) r := by
  classical
  obtain ⟨T, j, hj, hTaff, hTint⟩ := exists_isOpenImmersion_isAffine_isIntegral D sY hY hint
  have := hTaff
  have := hTint
  obtain ⟨t, ht⟩ : ∃ t : (BigFppfOver.toScheme D.site D.base D.base_mem).obj T,
      IsField (((BigFppfOver.toScheme D.site D.base D.base_mem).obj T).presheaf.stalk t) :=
    ⟨_, Field.toIsField ((BigFppfOver.toScheme D.site D.base D.base_mem).obj T).functionField⟩
  have hcol := isFinitePresentationColimit_residueCone D.site D.base D.base_mem T t ht
  let i₀ : AffineOpenNhds ((BigFppfOver.toScheme D.site D.base D.base_mem).obj T) t :=
    ⟨⟨⊤, Set.mem_univ t⟩, isAffineOpen_top _⟩
  have hV₀ : IsAffine ((BigFppfOver.toScheme D.site D.base D.base_mem).obj
      ((affineNhdsSystem D.site D.base D.base_mem T t).obj i₀)) :=
    isAffineOpen_top ((BigFppfOver.toScheme D.site D.base D.base_mem).obj T)
  obtain ⟨j₀, hj₀def⟩ :
      ∃ j₀ : yoneda.obj ((affineNhdsSystem D.site D.base D.base_mem T t).obj i₀) ⟶ Y,
      j₀ = yoneda.map (opensObjectι D.site D.base D.base_mem T i₀.obj.1) ≫ j := ⟨_, rfl⟩
  have hj₀ : IsOpenImmersion D.site D.base D.base_mem j₀ := by
    rw [hj₀def]
    exact isOpenImmersion_yoneda_map_opensObjectι_comp D.site D.base D.base_mem T _ hj
  obtain ⟨η, hηdef⟩ : ∃ η, η = pointsMap D.site D.base D.base_mem _ j
      ((schemePointRepresentative D.site D.base D.base_mem T t).class D.site D.base D.base_mem
        (yoneda.obj T)) := ⟨_, rfl⟩
  obtain ⟨φ, g, hgspec, hgsq⟩ := exists_ringEquiv_residueField_schemeResidueField_of_mono
    D.site D.base D.base_mem hY.1 (D.isDecentSpace_of_isGood sY hY) T j
    (mono_of_isOpenImmersion D.site D.base D.base_mem j hj) t η hηdef.symm
  have : IsIso g := isIso_of_isIso_toScheme_map D.site D.base D.base_mem g (by
    show IsIso (D.site.inclusion.map g.left)
    rw [hgspec]
    have : IsIso (CommRingCat.ofHom φ.toRingHom) :=
      (ConcreteCategory.isIso_iff_bijective _).2 φ.bijective
    exact (Scheme.Spec.mapIso (asIso (CommRingCat.ofHom φ.toRingHom)).op).isIso_hom)
  obtain ⟨Tf, a, b, hpb, e, he⟩ := hfib η
  have hpbT : IsPullback a (yoneda.map (b ≫ inv g)) f
      (yoneda.map (residueToAffineNhds D.site D.base D.base_mem T t i₀) ≫ j₀) :=
    isPullback_yoneda_map_comp_inv D.site D.base D.base_mem hpb g (by
      refine Eq.trans ?_ hgsq.symm
      rw [hj₀def]
      exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ j)
        ((yoneda.map_comp _ _).symm.trans (congrArg yoneda.map
          (residueToAffineNhds_comp_opensObjectι D.site D.base D.base_mem T t i₀)))))
  obtain ⟨ψ, hψ⟩ := exists_isPullback_affineSpaceProj_of_iso D.site D.base D.base_mem r hV₀ b g
    (residueToAffineNhds D.site D.base D.base_mem T t i₀) e he
  obtain ⟨Θ⟩ := nonempty_baseChange_iso_affineSpaceFinitePresentation D sX hX sY hY f hbase r hqc
    hV₀ (residueToAffineNhds D.site D.base D.base_mem T t i₀) j₀ hpbT hψ
  obtain ⟨jj, e', Θ', -⟩ := hcol.essIso i₀
    (baseChangeFinitePresentation D sX hX sY hY f hbase hqc j₀)
    (affineSpaceFinitePresentation D r _ hV₀) Θ
  exact exists_isPullback_isAffineSpaceBundle_of_baseChange_iso D sX hX sY hY f hbase r hqc t
    hV₀ e' j₀ hj₀ Θ'

end SpreadOut

end AlgebraicGeometry.Space

end
