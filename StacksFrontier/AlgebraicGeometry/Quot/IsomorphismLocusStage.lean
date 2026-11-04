module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceSiteFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenLiftOverHenselianPair
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# The isomorphism locus of a proper flat family, read on schemes

For morphisms of schemes `a : W ⟶ T` (locally of finite presentation, flat, universally closed),
`b : V ⟶ T` (proper) and `k : W ⟶ V` over `T`, Stacks 05XD gives an open subscheme `U ⊆ T` such
that a morphism `T' ⟶ T` factors through `U` exactly when the base change of `k` to `T'` is an
isomorphism.  This file reads the algebraic-space statement of Stacks 05XD on the site over `T` and
transports it to scheme morphisms, through the fact that the functor of points and the
underlying-scheme functor preserve and reflect the relevant isomorphisms.

## Main results

* `AlgebraicGeometry.Space.exists_opens_range_subset_iff_isIso_pullbackLift`: Stacks 05XD for
  scheme morphisms: an open `U ⊆ T` such that `T' ⟶ T` factors through `U` exactly when the base
  change of `k` to `T'` is an isomorphism.

## References

* [Stacks Project, Tag 05XD](https://stacks.math.columbia.edu/tag/05XD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)

/-- For `k : X ⟶ Y` over `Z` and `h : Z' ⟶ Z`, the image under `F` of the induced morphism
`X ×_Z Z' ⟶ Y ×_Z Z'` corresponds, through the comparisons `F (X ×_Z Z') ≅ F X ×_{F Z} F Z'` and
`F (Y ×_Z Z') ≅ F Y ×_{F Z} F Z'`, to the morphism induced by `F.map k`. -/
theorem map_pullbackLift_comp_preservesPullbackIso_hom {X Y Z Z' : C} (k : X ⟶ Y) (a : X ⟶ Z)
    (b : Y ⟶ Z) (hk : k ≫ b = a) (h : Z' ⟶ Z) [HasPullback a h] [HasPullback b h]
    [HasPullback (F.map a) (F.map h)] [HasPullback (F.map b) (F.map h)]
    [PreservesLimit (cospan a h) F] [PreservesLimit (cospan b h) F] :
    F.map (pullback.lift (f := b) (g := h) (pullback.fst a h ≫ k) (pullback.snd a h)
        (by rw [Category.assoc, hk, pullback.condition])) ≫ (PreservesPullback.iso F b h).hom =
      (PreservesPullback.iso F a h).hom ≫
        pullback.lift (f := F.map b) (g := F.map h) (pullback.fst (F.map a) (F.map h) ≫ F.map k)
          (pullback.snd (F.map a) (F.map h))
          (by rw [Category.assoc, ← F.map_comp, hk, pullback.condition]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, PreservesPullback.iso_hom_fst, ← F.map_comp, pullback.lift_fst,
      Category.assoc, pullback.lift_fst, ← Category.assoc, PreservesPullback.iso_hom_fst,
      F.map_comp]
  · rw [Category.assoc, PreservesPullback.iso_hom_snd, ← F.map_comp, pullback.lift_snd,
      Category.assoc, pullback.lift_snd, PreservesPullback.iso_hom_snd]

/-- For a functor `F` that reflects isomorphisms and preserves the two pullbacks, the morphism
`X ×_Z Z' ⟶ Y ×_Z Z'` induced by `k` is an isomorphism if and only if the morphism
`F X ×_{F Z} F Z' ⟶ F Y ×_{F Z} F Z'` induced by `F.map k` is. -/
theorem isIso_pullbackLift_iff_of_preserves [F.ReflectsIsomorphisms] {X Y Z Z' : C} (k : X ⟶ Y)
    (a : X ⟶ Z) (b : Y ⟶ Z) (hk : k ≫ b = a) (h : Z' ⟶ Z) [HasPullback a h] [HasPullback b h]
    [HasPullback (F.map a) (F.map h)] [HasPullback (F.map b) (F.map h)]
    [PreservesLimit (cospan a h) F] [PreservesLimit (cospan b h) F] :
    IsIso (pullback.lift (f := b) (g := h) (pullback.fst a h ≫ k) (pullback.snd a h)
        (by rw [Category.assoc, hk, pullback.condition])) ↔
      IsIso (pullback.lift (f := F.map b) (g := F.map h)
        (pullback.fst (F.map a) (F.map h) ≫ F.map k) (pullback.snd (F.map a) (F.map h))
        (by rw [Category.assoc, ← F.map_comp, hk, pullback.condition])) := by
  have key := F.map_pullbackLift_comp_preservesPullbackIso_hom k a b hk h
  rw [← Iso.eq_comp_inv] at key
  rw [← isIso_iff_of_reflects_iso _ F, key, isIso_comp_right_iff, isIso_comp_left_iff]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u})

/-- The morphism `f : X ⟶ T` as a morphism over `T` in the site, to the object given by `𝟙 T`. -/
private abbrev siteHomToBase {T X : Scheme.{u}} (hT : B.Contains T) (hX : B.Contains X)
    (f : X ⟶ T) : siteObject B T hT hX f ⟶ siteObject B T hT hT (𝟙 T) :=
  Over.homMk (ObjectProperty.homMk f) (ObjectProperty.hom_ext _ (Category.comp_id f))

/-- Let `a : W ⟶ T` be locally of finite presentation, flat and universally closed, `b : V ⟶ T`
proper, and `k : W ⟶ V` a morphism over `T`. Then there is an open `U ⊆ T` such that a morphism
`g : T' ⟶ T` factors through `U` if and only if the base change `W ×_T T' ⟶ V ×_T T'` of `k` is an
isomorphism. -/
theorem exists_opens_range_subset_iff_isIso_pullbackLift {T W V : Scheme.{u}}
    (hT : B.Contains T) (hW : B.Contains W) (hV : B.Contains V) (a : W ⟶ T) (b : V ⟶ T)
    (k : W ⟶ V) (hk : k ≫ b = a) [LocallyOfFinitePresentation a] [Flat a]
    [_root_.AlgebraicGeometry.UniversallyClosed a] [_root_.AlgebraicGeometry.IsProper b] :
    ∃ U : T.Opens, ∀ (T' : Scheme.{u}) (_ : B.Contains T') (g : T' ⟶ T),
      Set.range g ⊆ U ↔ IsIso (pullback.lift (f := b) (g := g) (pullback.fst a g ≫ k)
        (pullback.snd a g) (by rw [Category.assoc, hk, pullback.condition])) := by
  have := preservesLimitsOfShape_walkingCospan_toScheme B T hT
  let tT : BigFppfOver B T hT := siteObject B T hT hT (𝟙 T)
  let tW : BigFppfOver B T hT := siteObject B T hT hW a
  let tV : BigFppfOver B T hT := siteObject B T hT hV b
  let aa : tW ⟶ tT := siteHomToBase B hT hW a
  let bb : tV ⟶ tT := siteHomToBase B hT hV b
  let kk : tW ⟶ tV := Over.homMk (ObjectProperty.homMk k) (ObjectProperty.hom_ext _ hk)
  have hkk : kk ≫ bb = aa := Over.OverMorphism.ext (ObjectProperty.hom_ext _ hk)
  have hbb : IsProper B T hT (yoneda.map bb) := (isProper_yoneda_map_iff B T hT bb).2 ‹_›
  obtain ⟨Wsub, hWsub, hWprop⟩ := exists_isOpenSubspace_iff_isIso_baseChange B T hT
    (isAlgebraicSpace_yoneda B T hT tW) (isAlgebraicSpace_yoneda B T hT tV)
    (isAlgebraicSpace_yoneda B T hT tT) (yoneda.map kk) (yoneda.map aa) (yoneda.map bb)
    (by rw [← Functor.map_comp, hkk])
    (isLocallyOfFinitePresentation_yoneda_map B T hT aa ‹_›) (isFlat_yoneda_map B T hT aa ‹_›)
    (universallyClosed_yoneda_map B T hT aa ‹_›)
    ((isLocallyOfFiniteType_yoneda_map_iff B T hT bb).2
      (by show LocallyOfFiniteType b; infer_instance))
    (isClosed_of_universallyClosed B T hT (isAlgebraicSpace_yoneda B T hT tT) _ hbb.2.2) hbb.1
  obtain ⟨V', s, hs, hfac⟩ := exists_isOpenImmersion_forall_factorsThrough_iff B T hT Wsub hWsub.2
  have hs' : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B T hT).map s) := hs
  let U : T.Opens := ((BigFppfOver.toScheme B T hT).map s).opensRange
  refine ⟨U, fun T' hT' g => ?_⟩
  let tT' : BigFppfOver B T hT := siteObject B T hT hT' g
  let hh : tT' ⟶ tT := siteHomToBase B hT hT' g
  have hV'hom : V'.hom.hom = (BigFppfOver.toScheme B T hT).map s := by
    rw [← Over.w s]
    exact Category.comp_id (s.left.hom)
  have step1 : Set.range g ⊆ (U : Set T) ↔
      ∃ t : tT' ⟶ V', t ≫ s = hh := by
    constructor
    · intro hg
      let l := IsOpenImmersion.lift ((BigFppfOver.toScheme B T hT).map s) g
        (fun x hx => by
          have hx' := hg hx
          rwa [Scheme.Hom.coe_opensRange] at hx')
      have hl : l ≫ (BigFppfOver.toScheme B T hT).map s = g := IsOpenImmersion.lift_fac _ _ _
      refine ⟨Over.homMk (ObjectProperty.homMk l) (ObjectProperty.hom_ext _ ?_), ?_⟩
      · show l ≫ V'.hom.hom = g
        rw [hV'hom, hl]
      · exact Over.OverMorphism.ext (ObjectProperty.hom_ext _ hl)
    · rintro ⟨t, ht⟩ x ⟨y, rfl⟩
      refine ⟨((BigFppfOver.toScheme B T hT).map t) y, ?_⟩
      show ((BigFppfOver.toScheme B T hT).map s) (((BigFppfOver.toScheme B T hT).map t) y) =
        ((BigFppfOver.toScheme B T hT).map hh) y
      rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, ht]
  rw [step1, hfac tT' hh,
    hWprop (yoneda.obj tT') (isAlgebraicSpace_yoneda B T hT tT') (yoneda.map hh)]
  refine (Functor.isIso_pullbackLift_iff_of_preserves yoneda kk aa bb hkk hh).symm.trans ?_
  exact Functor.isIso_pullbackLift_iff_of_preserves (BigFppfOver.toScheme B T hT) kk aa bb hkk hh

end AlgebraicGeometry.Space
