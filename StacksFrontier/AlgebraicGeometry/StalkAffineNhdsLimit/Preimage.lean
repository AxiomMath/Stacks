module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
public import StacksFrontier.AlgebraicGeometry.StalkAffineNhdsLimit.Basic

/-!
# `X ×_S Spec 𝒪_{S, s}` is the inverse limit of the preimages of the affine neighbourhoods of `s`

Let `f : X ⟶ S` be a morphism of schemes and `s` a point of `S`. The preimages `f⁻¹(W)` of the
affine open neighbourhoods `W` of `s` form a cofiltered diagram of open subschemes of `X`, with
affine transition morphisms. This file proves that `X ×_S Spec 𝒪_{S, s}` is its limit.

## Main definitions

* `AlgebraicGeometry.preimageAffineOpenNhdsDiagram`: the diagram `W ↦ f⁻¹(W)`.
* `AlgebraicGeometry.preimageSpecStalkCone`: the cone on it with apex `X ×_S Spec 𝒪_{S, s}`.

## Main results

* `AlgebraicGeometry.isLimitPreimageSpecStalkCone`: that cone is a limit cone.
* `AlgebraicGeometry.isAffineHom_preimageAffineOpenNhdsDiagram_map`: the transition morphisms are
  affine; for `f` quasi-compact (resp. quasi-separated) the stages are quasi-compact (resp.
  quasi-separated).

## References

* [Stacks Project, Tag 01YX](https://stacks.math.columbia.edu/tag/01YX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) (s : S)

/-- The underlying open of an affine open neighbourhood of `s`. -/
abbrev AffineOpenNhds.opens {s : S} (W : AffineOpenNhds S s) : S.Opens :=
  (OpenNhds.inclusion s).obj W.obj

/-- The underlying open of an affine open neighbourhood `W` is the open of `W.obj`. -/
lemma AffineOpenNhds.opens_eq {s : S} (W : AffineOpenNhds S s) : W.opens = W.obj.1 :=
  rfl

/-- The point `s` lies in the underlying open of each of its affine open neighbourhoods. -/
lemma AffineOpenNhds.mem_opens {s : S} (W : AffineOpenNhds S s) : s ∈ W.opens :=
  W.obj.2

/-- A morphism of affine open neighbourhoods is an inclusion of their underlying opens. -/
lemma AffineOpenNhds.opens_le {s : S} {W W' : AffineOpenNhds S s} (g : W ⟶ W') :
    W.opens ≤ W'.opens :=
  leOfHom ((OpenNhds.inclusion s).map ((affineOpenNhds S s).ι.map g))

/-- The preimages `f⁻¹(W)` of the affine open neighbourhoods `W` of `s`, as a diagram of open
subschemes of `X`. -/
noncomputable def preimageAffineOpenNhdsDiagram : AffineOpenNhds S s ⥤ Scheme.{u} where
  obj W := (f ⁻¹ᵁ W.opens).toScheme
  map {W W'} g := X.homOfLE (U := f ⁻¹ᵁ W.opens) (V := f ⁻¹ᵁ W'.opens)
    (Scheme.Hom.preimage_mono f (AffineOpenNhds.opens_le g))
  map_id W := by simp
  map_comp g g' := by simp

/-- The value of `W ↦ f⁻¹(W)` at `W` is the open subscheme `f⁻¹(W)` of `X`. -/
@[simp]
lemma preimageAffineOpenNhdsDiagram_obj (W : AffineOpenNhds S s) :
    (preimageAffineOpenNhdsDiagram f s).obj W = (f ⁻¹ᵁ W.opens).toScheme :=
  rfl

/-- The transition morphism of `W ↦ f⁻¹(W)` along `W ⟶ W'` is the inclusion `f⁻¹(W) ⟶ f⁻¹(W')`. -/
lemma preimageAffineOpenNhdsDiagram_map {W W' : AffineOpenNhds S s} (g : W ⟶ W') :
    (preimageAffineOpenNhdsDiagram f s).map g =
      X.homOfLE (Scheme.Hom.preimage_mono f (AffineOpenNhds.opens_le g)) :=
  rfl

/-- The transition morphisms of `W ↦ f⁻¹(W)` commute with the inclusions of the opens `f⁻¹(W)` into
`X`. -/
@[reassoc (attr := simp)]
lemma preimageAffineOpenNhdsDiagram_map_ι {W W' : AffineOpenNhds S s} (g : W ⟶ W') :
    (preimageAffineOpenNhdsDiagram f s).map g ≫ (f ⁻¹ᵁ W'.opens).ι = (f ⁻¹ᵁ W.opens).ι :=
  X.homOfLE_ι (Scheme.Hom.preimage_mono f (AffineOpenNhds.opens_le g))

/-- The transition morphism of the diagram of affine open neighbourhoods of `s` along `W ⟶ W'` is
the inclusion `W ⟶ W'`. -/
lemma affineOpenNhdsDiagram_map_eq {W W' : AffineOpenNhds S s} (g : W ⟶ W') :
    (affineOpenNhdsDiagram S s).map g = S.homOfLE (AffineOpenNhds.opens_le g) :=
  rfl

/-- The restrictions `f⁻¹(W) ⟶ W` of `f`, as a natural transformation to the diagram of affine open
neighbourhoods of `s`. -/
noncomputable def preimageAffineOpenNhdsDiagramToBase :
    preimageAffineOpenNhdsDiagram f s ⟶ affineOpenNhdsDiagram S s where
  app W := f ∣_ W.opens
  naturality {W W'} g := by
    change X.homOfLE (Scheme.Hom.preimage_mono f (AffineOpenNhds.opens_le g)) ≫ f ∣_ W'.opens =
      f ∣_ W.opens ≫ S.homOfLE (AffineOpenNhds.opens_le g)
    rw [← cancel_mono W'.opens.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
      Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc, morphismRestrict_ι]

/-- The component at `W` of the restrictions `f⁻¹(W) ⟶ W` is `f ∣_ W`. -/
@[simp]
lemma preimageAffineOpenNhdsDiagramToBase_app (W : AffineOpenNhds S s) :
    (preimageAffineOpenNhdsDiagramToBase f s).app W = f ∣_ W.opens :=
  rfl

/-- The first projection `X ×_S Spec 𝒪_{S, s} ⟶ X` lands in `f⁻¹(W)` for every affine open
neighbourhood `W` of `s`. -/
lemma range_pullback_fst_fromSpecStalk_subset (W : AffineOpenNhds S s) :
    Set.range (pullback.fst f (S.fromSpecStalk s)) ⊆ Set.range (f ⁻¹ᵁ W.opens).ι := by
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  show f (pullback.fst f (S.fromSpecStalk s) x) ∈ W.opens
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  have hx : S.fromSpecStalk s (pullback.snd f (S.fromSpecStalk s) x) ∈ Set.range
      (S.fromSpecStalk s) := ⟨_, rfl⟩
  rw [Scheme.range_fromSpecStalk] at hx
  exact hx.mem_open W.opens.isOpen W.mem_opens

/-- The leg `X ×_S Spec 𝒪_{S, s} ⟶ f⁻¹(W)`: the first projection, which lands in `f⁻¹(W)`. -/
noncomputable def preimageSpecStalkLeg (W : AffineOpenNhds S s) :
    pullback f (S.fromSpecStalk s) ⟶ (f ⁻¹ᵁ W.opens).toScheme :=
  IsOpenImmersion.lift (f ⁻¹ᵁ W.opens).ι (pullback.fst f (S.fromSpecStalk s))
    (range_pullback_fst_fromSpecStalk_subset f s W)

/-- The leg `X ×_S Spec 𝒪_{S, s} ⟶ f⁻¹(W)` followed by the inclusion of `f⁻¹(W)` into `X` is the
first projection. -/
@[reassoc (attr := simp)]
lemma preimageSpecStalkLeg_ι (W : AffineOpenNhds S s) :
    preimageSpecStalkLeg f s W ≫ (f ⁻¹ᵁ W.opens).ι = pullback.fst f (S.fromSpecStalk s) :=
  IsOpenImmersion.lift_fac _ _ _

/-- The leg `X ×_S Spec 𝒪_{S, s} ⟶ f⁻¹(W)` followed by `f ∣_ W` is the second projection followed
by `Spec 𝒪_{S, s} ⟶ W`. -/
@[reassoc]
lemma preimageSpecStalkLeg_morphismRestrict (W : AffineOpenNhds S s) :
    preimageSpecStalkLeg f s W ≫ f ∣_ W.opens =
      pullback.snd f (S.fromSpecStalk s) ≫ W.opens.fromSpecStalkOfMem s W.mem_opens := by
  rw [← cancel_mono W.opens.ι, Category.assoc, morphismRestrict_ι,
    preimageSpecStalkLeg_ι_assoc, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
    pullback.condition]

/-- The cone on `W ↦ f⁻¹(W)` with apex `X ×_S Spec 𝒪_{S, s}`. -/
noncomputable def preimageSpecStalkCone : Cone (preimageAffineOpenNhdsDiagram f s) where
  pt := pullback f (S.fromSpecStalk s)
  π :=
  { app := preimageSpecStalkLeg f s
    naturality {W W'} g := by
      change 𝟙 _ ≫ preimageSpecStalkLeg f s W' =
        preimageSpecStalkLeg f s W ≫
          X.homOfLE (Scheme.Hom.preimage_mono f (AffineOpenNhds.opens_le g))
      rw [← cancel_mono (f ⁻¹ᵁ W'.opens).ι]
      simp only [Category.assoc, Category.id_comp, Scheme.homOfLE_ι, preimageSpecStalkLeg_ι] }

/-- The apex of the cone on `W ↦ f⁻¹(W)` is `X ×_S Spec 𝒪_{S, s}`. -/
@[simp]
lemma preimageSpecStalkCone_pt :
    (preimageSpecStalkCone f s).pt = pullback f (S.fromSpecStalk s) :=
  rfl

/-- The leg at `W` of the cone on `W ↦ f⁻¹(W)` is `AlgebraicGeometry.preimageSpecStalkLeg`. -/
@[simp]
lemma preimageSpecStalkCone_π_app (W : AffineOpenNhds S s) :
    (preimageSpecStalkCone f s).π.app W = preimageSpecStalkLeg f s W :=
  rfl

/-- The square formed by the leg `X ×_S Spec 𝒪_{S, s} ⟶ f⁻¹(W)`, the second projection, `f ∣_ W`
and `Spec 𝒪_{S, s} ⟶ W` is cartesian. -/
lemma isPullback_preimageSpecStalkLeg (W : AffineOpenNhds S s) :
    IsPullback (preimageSpecStalkLeg f s W) (pullback.snd f (S.fromSpecStalk s))
      (f ∣_ W.opens) (W.opens.fromSpecStalkOfMem s W.mem_opens) := by
  refine IsPullback.of_right ?_ (preimageSpecStalkLeg_morphismRestrict f s W)
    (isPullback_morphismRestrict f W.opens).flip
  rw [preimageSpecStalkLeg_ι, Scheme.Opens.fromSpecStalkOfMem_ι]
  exact IsPullback.of_hasPullback f (S.fromSpecStalk s)

attribute [local instance] IsCofiltered.isConnected in
/-- **`X ×_S Spec 𝒪_{S, s}` is the limit of the preimages `f⁻¹(W)` of the affine open
neighbourhoods `W` of `s`.** -/
noncomputable def isLimitPreimageSpecStalkCone : IsLimit (preimageSpecStalkCone f s) :=
  isLimitOfIsPullbackOfIsConnected (preimageAffineOpenNhdsDiagramToBase f s)
    (preimageSpecStalkCone f s) (specStalkCone S s)
    { hom := pullback.snd f (S.fromSpecStalk s)
      w := fun W ↦ (preimageSpecStalkLeg_morphismRestrict f s W).symm }
    (fun W ↦ isPullback_preimageSpecStalkLeg f s W) (isLimitSpecStalkCone S s)

/-- The square formed by the transition morphisms `f⁻¹(W) ⟶ f⁻¹(W')` and `W ⟶ W'` and the
restrictions `f ∣_ W` and `f ∣_ W'` is cartesian. -/
lemma isPullback_preimageAffineOpenNhdsDiagram_map {W W' : AffineOpenNhds S s} (g : W ⟶ W') :
    IsPullback ((preimageAffineOpenNhdsDiagram f s).map g) (f ∣_ W.opens) (f ∣_ W'.opens)
      ((affineOpenNhdsDiagram S s).map g) := by
  refine IsPullback.of_right ?_ ((preimageAffineOpenNhdsDiagramToBase f s).naturality g)
    (isPullback_morphismRestrict f W'.opens).flip
  rw [preimageAffineOpenNhdsDiagram_map_ι, affineOpenNhdsDiagram_map_eq, Scheme.homOfLE_ι]
  exact (isPullback_morphismRestrict f W.opens).flip

/-- The transition morphisms of `W ↦ f⁻¹(W)` are affine. -/
instance isAffineHom_preimageAffineOpenNhdsDiagram_map {W W' : AffineOpenNhds S s}
    (g : W ⟶ W') : IsAffineHom ((preimageAffineOpenNhdsDiagram f s).map g) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom)
    (isPullback_preimageAffineOpenNhdsDiagram_map f s g).flip
    (isAffineHom_affineOpenNhdsDiagram_map S s g)

/-- For `f` quasi-compact, the preimage `f⁻¹(W)` of an affine open neighbourhood `W` of `s` is
quasi-compact. -/
instance compactSpace_preimageAffineOpenNhdsDiagram_obj [QuasiCompact f]
    (W : AffineOpenNhds S s) : CompactSpace ((preimageAffineOpenNhdsDiagram f s).obj W) :=
  @QuasiCompact.compactSpace_of_compactSpace _ _ (f ∣_ W.opens)
    (MorphismProperty.of_isPullback (P := @QuasiCompact)
      (isPullback_morphismRestrict f W.opens).flip ‹_›)
    (compactSpace_affineOpenNhdsDiagram_obj S s W)

/-- For `f` quasi-separated, the preimage `f⁻¹(W)` of an affine open neighbourhood `W` of `s` is
quasi-separated. -/
instance quasiSeparatedSpace_preimageAffineOpenNhdsDiagram_obj [QuasiSeparated f]
    (W : AffineOpenNhds S s) : QuasiSeparatedSpace ((preimageAffineOpenNhdsDiagram f s).obj W) :=
  @quasiSeparatedSpace_of_quasiSeparated _ _ (f ∣_ W.opens)
    (quasiSeparatedSpace_affineOpenNhdsDiagram_obj S s W)
    (MorphismProperty.of_isPullback (P := @QuasiSeparated)
      (isPullback_morphismRestrict f W.opens).flip ‹_›)

end AlgebraicGeometry

end
