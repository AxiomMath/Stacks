module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesFiniteSingularities
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedPointInfiniteFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteProperQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericallyFiniteQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# The open locus of the base over which a family of curves has finite singular locus

For a family of curves `f : X → S` let `Z ⊂ X` be the closed set of points at which `f` is not
smooth. The set of points `s` of `S` over which `Z` has only finitely many points is open, and
its formation commutes with arbitrary base change. Consequently there is an open subspace `W` of
`S` such that a family of curves `F` mapping to the given one satisfies the defining condition of
`Curves⁺` exactly when its morphism of base schemes factors through `W`. This is the openness
half of Tag 0DZW.

## Main definitions

* `AlgebraicGeometry.CurveFamily.finiteNonSmoothBaseLocus`: the set of points of the base over
  which the non-smooth locus of a family of curves has finitely many points.

## Main results

* `AlgebraicGeometry.Space.finite_setOf_pointsMap_eq_iff_of_isPullback`: for a proper morphism
  of algebraic spaces with decent target and a base change of it along a morphism from a decent
  space, the fibre of the base change over a point is finite exactly when the fibre of the
  original morphism over the image point is.
* `AlgebraicGeometry.CurveFamily.isOpen_finiteNonSmoothBaseLocus`: the locus is open.
* `AlgebraicGeometry.CurveFamily.preimage_finiteNonSmoothBaseLocus`: its formation commutes with
  base change along a morphism of families.
* `AlgebraicGeometry.CurveFamily.isFiniteNonSmoothLocus_iff_finiteNonSmoothBaseLocus_eq_univ`:
  a family of curves lies in `Curves⁺` exactly when the locus is its whole base.
* `AlgebraicGeometry.CurveFamily.exists_isOpenSubspace_finiteNonSmoothLocus`: the open subspace
  of the base through which a morphism of base schemes factors exactly when the source family
  lies in `Curves⁺`.

## Implementation notes

Everything is read on point sets. The reduced closed subspace `Z` supported on the non-smooth
locus is proper over the base, and for a proper morphism between decent spaces a fibre is finite
exactly when the morphism is quasi-finite at each of its points (Tag 0ACK). Hence the
complement of the locus is the image under the closed map `Z → S` of the closed set where
`Z → S` is not quasi-finite (part (1) of Tag 0ABM), which gives openness. For a morphism of
families `F → G` the non-smooth locus of `F` is the preimage of that of `G` (Tag 02V4, the flat
case), so it is the point set of the base change `P` of `Z` to the total space of `F`, and `P` is
the base change of `Z → S` to the base of `F`. Part (2) of Tag 0ABM together with the
surjectivity of the points of a fibre product onto compatible pairs (Tag 03H4) then compares
the fibres of `P` and of `Z`. Finally, `Z → S` is finite exactly when it is locally
quasi-finite, `Z → S` being proper (Tag 0A4X), that is exactly when every fibre of `Z → S` is
finite; and every fibre of the reduced closed subspace of the definition of `Curves⁺` is the
set of non-smooth points over the given point, its inclusion being injective on points.

## References

* [Stacks Project, Tag 0DZW](https://stacks.math.columbia.edu/tag/0DZW)
* [Stacks Project, Tag 0A4X](https://stacks.math.columbia.edu/tag/0A4X)
* [Stacks Project, Tag 0ABM](https://stacks.math.columbia.edu/tag/0ABM)
* [Stacks Project, Tag 0ACK](https://stacks.math.columbia.edu/tag/0ACK)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- For a monomorphism `i : Y ⟶ X` of presheaves whose image on points is `R` and a morphism
`h : X ⟶ T`, the fibre of `i ≫ h` over a point `t` is finite exactly when the set of points of `R`
lying over `t` is finite, a monomorphism being injective on points. -/
theorem finite_setOf_pointsMap_comp_eq_iff_of_mono {Y X T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (i : Y ⟶ X) [Mono i] {R : Set (points B S hS X)} (hR : Set.range (pointsMap B S hS Y i) = R)
    (h : X ⟶ T) (t : points B S hS T) :
    {y | pointsMap B S hS Y (i ≫ h) y = t}.Finite ↔
      {x | x ∈ R ∧ pointsMap B S hS X h x = t}.Finite := by
  subst hR
  have heq : {x | x ∈ Set.range (pointsMap B S hS Y i) ∧ pointsMap B S hS X h x = t} =
      pointsMap B S hS Y i '' {y | pointsMap B S hS Y (i ≫ h) y = t} := by
    ext x
    constructor
    · rintro ⟨⟨y, rfl⟩, hy⟩
      exact ⟨y, by rwa [Set.mem_ofPred_eq, pointsMap_comp_apply], rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, rfl⟩, by rwa [Set.mem_ofPred_eq, pointsMap_comp_apply] at hy⟩
  rw [heq, Set.finite_image_iff (pointsMap_injective_of_mono B S hS i).injOn]

/-- The source of a separated morphism of algebraic spaces with decent target is decent. -/
private theorem isDecentSpace_source_of_isSeparated {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (hf : IsSeparated B S hS f.hom) (hY : IsDecentSpace B S hS Y.obj) :
    IsDecentSpace B S hS X.obj :=
  isDecentSpace_source_of_isQuasiSeparated B S hS X.property Y.property f.hom
    (isQuasiSeparated_of_isSeparated B S hS hf) hY

/-- In a cartesian square of algebraic spaces over `S` whose base change `p` is taken of a proper
morphism `f` with decent target, along a morphism from a decent space, the fibre of `p` over a
point is finite exactly when the fibre of `f` over the image point is finite. -/
theorem finite_setOf_pointsMap_eq_iff_of_isPullback {W Z X Y : AlgebraicSpaces B S hS}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f)
    (hf : IsProper B S hS f.hom) (hYdec : IsDecentSpace B S hS Y.obj)
    (hZdec : IsDecentSpace B S hS Z.obj) (z : points B S hS Z.obj) :
    {w | pointsMap B S hS W.obj p.hom w = z}.Finite ↔
      {x | pointsMap B S hS X.obj f.hom x = pointsMap B S hS Z.obj g.hom z}.Finite := by
  have hp : IsProper B S hS p.hom :=
    (isProper_isStableUnderBaseChange B S hS).of_isPullback sq.flip hf
  have sq' := AlgebraicSpaces.isPullback_hom B S hS sq
  have hXdec := isDecentSpace_source_of_isSeparated B S hS hf.1 hYdec
  have hWdec := isDecentSpace_source_of_isSeparated B S hS hp.1 hZdec
  rw [finite_fibre_iff_forall_isQuasiFiniteAt B S hS W.property Z.property p.hom hp.2.1.1
      hp.2.2 hWdec hZdec z,
    finite_fibre_iff_forall_isQuasiFiniteAt B S hS X.property Y.property f.hom hf.2.1.1 hf.2.2
      hXdec hYdec _]
  constructor
  · intro h x hx
    obtain ⟨w, hw, rfl⟩ := exists_points_of_isPullback B S hS sq' z x hx.symm
    exact (isQuasiFiniteAt_iff_of_isPullback B S hS sq' X.property Y.property Z.property
      hf.2.1.1 w).mp (h w hw)
  · intro h w hw
    refine (isQuasiFiniteAt_iff_of_isPullback B S hS sq' X.property Y.property Z.property
      hf.2.1.1 w).mpr (h _ ?_)
    rw [← pointsMap_apply_comm B S hS sq'.w w, hw]

end Space

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

namespace CurveFamily

attribute [local instance] Space.pointTopology

/-- Pullbacks of presheaves on `BigFppfOver B integerBase hZ`, given directly: instance search
for them times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_CurvesPlusOpen :
    HasPullbacks ((BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_CurvesPlusOpen
    {X Y Z : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_CurvesPlusOpen B hZ).has_limit _

/-- The set of points of the base of a family of curves over which the set of points of the
total space at which the structure morphism is not smooth is finite. -/
def finiteNonSmoothBaseLocus (X : CurveFamily B hZ) :
    Set (Space.points B integerBase hZ (schemeSpace X.base).obj) :=
  {t | {x : Space.points B integerBase hZ X.total.obj |
    ¬ Space.IsSmoothAt B integerBase hZ X.toBase.hom x ∧
      Space.pointsMap B integerBase hZ X.total.obj X.toBase.hom x = t}.Finite}

/-- The total space of a family of curves is decent: its structure morphism is separated and
its base is a scheme. -/
theorem isDecentSpace_total (X : CurveFamily B hZ) :
    Space.IsDecentSpace B integerBase hZ X.total.obj :=
  Space.isDecentSpace_source_of_isSeparated B integerBase hZ X.proper.1
    (Space.isDecentSpace_yoneda B integerBase hZ X.base)

/-- For a closed subspace `Z` of the total space whose points are the non-smooth points and which
is proper over the base, there are finitely many non-smooth points over a point `t` of the base
exactly when `Z` is quasi-finite over the base at every point of `Z` above `t`. -/
theorem finite_nonSmoothFibre_iff_forall_isQuasiFiniteAt (X : CurveFamily B hZ)
    (Z : Subfunctor X.total.obj)
    (hZcl : Space.IsClosedSubspace B integerBase hZ Z)
    (hrange : Set.range (Space.pointsMap B integerBase hZ Z.toFunctor Z.ι) =
      {x : Space.points B integerBase hZ X.total.obj |
        ¬ Space.IsSmoothAt B integerBase hZ X.toBase.hom x})
    (hp : Space.IsProper B integerBase hZ (Z.ι ≫ X.toBase.hom))
    (t : Space.points B integerBase hZ (schemeSpace X.base).obj) :
    {x : Space.points B integerBase hZ X.total.obj |
      ¬ Space.IsSmoothAt B integerBase hZ X.toBase.hom x ∧
        Space.pointsMap B integerBase hZ X.total.obj X.toBase.hom x = t}.Finite ↔
      ∀ z, Space.pointsMap B integerBase hZ Z.toFunctor (Z.ι ≫ X.toBase.hom) z = t →
        Space.IsQuasiFiniteAt B integerBase hZ (Z.ι ≫ X.toBase.hom) z :=
  (Space.finite_setOf_pointsMap_comp_eq_iff_of_mono B integerBase hZ Z.ι hrange
    X.toBase.hom t).symm.trans
      (Space.finite_fibre_iff_forall_isQuasiFiniteAt B integerBase hZ hZcl.1
        (schemeSpace X.base).property _ hp.2.1.1 hp.2.2
        (Space.isDecentSpace_of_isClosedSubspace B integerBase hZ (isDecentSpace_total B hZ X)
          hZcl)
        (Space.isDecentSpace_yoneda B integerBase hZ X.base) t)

/-- The reduced closed subspace of the total space of a family of curves supported on the
non-smooth locus: a closed subspace whose points are the non-smooth points, which is reduced
and proper over the base. -/
theorem exists_isClosedSubspace_nonSmooth (X : CurveFamily B hZ) :
    ∃ Z : Subfunctor X.total.obj, Space.IsClosedSubspace B integerBase hZ Z ∧
      Set.range (Space.pointsMap B integerBase hZ Z.toFunctor Z.ι) =
        {x : Space.points B integerBase hZ X.total.obj |
          ¬ Space.IsSmoothAt B integerBase hZ X.toBase.hom x} ∧
      Space.HasEtaleLocalProperty B integerBase hZ Z.toFunctor
        (fun Y : Scheme.{u} => IsReduced Y) ∧
      Space.IsProper B integerBase hZ (Z.ι ≫ X.toBase.hom) := by
  have hN : IsClosed {x : Space.points B integerBase hZ X.total.obj |
      ¬ Space.IsSmoothAt B integerBase hZ X.toBase.hom x} :=
    (Space.isOpen_setOf_isSmoothAt B integerBase hZ X.total.property X.toBase.hom).isClosed_compl
  have hZcl := Space.isClosedSubspace_reducedClosedSubspace B integerBase hZ _
    X.total.property _ hN
  exact ⟨_, hZcl,
    Space.range_pointsMap_ι_reducedClosedSubspace B integerBase hZ _ X.total.property _ hN,
    Space.hasEtaleLocalProperty_isReduced_reducedClosedSubspace B integerBase hZ _
      X.total.property _ hN,
    Space.isProper_comp B integerBase hZ hZcl.1 X.total.property (schemeSpace X.base).property _
      _ (Space.isProper_ι_reducedClosedSubspace B integerBase hZ _ X.total.property _ hN)
      X.proper⟩

/-- A family of curves lies in `Curves⁺` exactly when over every point of its base there are
only finitely many points at which its structure morphism is not smooth. -/
theorem isFiniteNonSmoothLocus_iff_finiteNonSmoothBaseLocus_eq_univ (X : CurveFamily B hZ) :
    IsFiniteNonSmoothLocus B hZ X ↔ finiteNonSmoothBaseLocus B hZ X = Set.univ := by
  have hY := (schemeSpace X.base).property
  constructor
  · rintro ⟨Z, hZcl, hrange, -, hfin⟩
    obtain ⟨hp, hlqf⟩ := Space.isProper_and_isLocallyQuasiFinite_of_isFinite B integerBase hZ
      hZcl.1 hY _ hfin
    rw [Space.isLocallyQuasiFinite_iff_forall_isQuasiFiniteAt B integerBase hZ hZcl.1 hY]
      at hlqf
    exact Set.eq_univ_of_forall fun t =>
      (finite_nonSmoothFibre_iff_forall_isQuasiFiniteAt B hZ X Z hZcl hrange hp t).mpr
        fun z _ => hlqf z
  · intro h
    obtain ⟨Z, hZcl, hrange, hred, hp⟩ := exists_isClosedSubspace_nonSmooth B hZ X
    exact ⟨Z, hZcl, hrange, hred,
      Space.isFinite_of_isProper_of_isLocallyQuasiFinite B integerBase hZ hZcl.1 hY _ hp
        ((Space.isLocallyQuasiFinite_iff_forall_isQuasiFiniteAt B integerBase hZ hZcl.1 hY
          _).mpr fun z =>
            (finite_nonSmoothFibre_iff_forall_isQuasiFiniteAt B hZ X Z hZcl hrange hp _).mp
              (Set.eq_univ_iff_forall.mp h _) z rfl)⟩

/-- The locus of the base over which there are only finitely many non-smooth points is open: its
complement is the image, under the closed morphism from the reduced non-smooth locus to the
base, of the closed set where that morphism is not quasi-finite. -/
theorem isOpen_finiteNonSmoothBaseLocus (X : CurveFamily B hZ) :
    IsOpen (finiteNonSmoothBaseLocus B hZ X) := by
  obtain ⟨Z, hZcl, hrange, -, hp⟩ := exists_isClosedSubspace_nonSmooth B hZ X
  have hcompl : (finiteNonSmoothBaseLocus B hZ X)ᶜ =
      Space.pointsMap B integerBase hZ Z.toFunctor (Z.ι ≫ X.toBase.hom) ''
        {z | Space.IsQuasiFiniteAt B integerBase hZ (Z.ι ≫ X.toBase.hom) z}ᶜ := by
    ext t
    have hmem : t ∈ finiteNonSmoothBaseLocus B hZ X ↔ _ :=
      finite_nonSmoothFibre_iff_forall_isQuasiFiniteAt B hZ X Z hZcl hrange hp t
    rw [Set.mem_compl_iff, hmem]
    simp only [not_forall, Set.mem_image, Set.mem_compl_iff, Set.mem_ofPred_eq]
    exact ⟨fun ⟨z, hz, hq⟩ => ⟨z, hq, hz⟩, fun ⟨z, hq, hz⟩ => ⟨z, hz, hq⟩⟩
  rw [← isClosed_compl_iff, hcompl]
  exact Space.isClosed_of_universallyClosed B integerBase hZ (schemeSpace X.base).property _
    hp.2.2 _ (Space.isOpen_setOf_isQuasiFiniteAt B integerBase hZ _).isClosed_compl

/-- The locus of the base over which there are only finitely many non-smooth points commutes
with base change: for a morphism of families of curves, the locus of the source is the inverse
image of the locus of the target under the morphism of base schemes. -/
theorem preimage_finiteNonSmoothBaseLocus {X Y : CurveFamily B hZ} (φ : X ⟶ Y) :
    Space.pointsMap B integerBase hZ (schemeSpace X.base).obj (schemeSpaceMap φ.baseMap).hom ⁻¹'
        finiteNonSmoothBaseLocus B hZ Y =
      finiteNonSmoothBaseLocus B hZ X := by
  obtain ⟨Z, hZcl, hrange, -, hp⟩ := exists_isClosedSubspace_nonSmooth B hZ Y
  let Zb : AlgebraicSpaces B integerBase hZ := ⟨Z.toFunctor, hZcl.1⟩
  let ι : Zb ⟶ Y.total := ObjectProperty.homMk Z.ι
  have sq₁ := IsPullback.of_hasPullback ι φ.totalMap
  have sq₂ := (sq₁.paste_vert φ.cartesian).flip
  have sq₁' := AlgebraicSpaces.isPullback_hom B integerBase hZ sq₁
  have : Mono (pullback.snd ι φ.totalMap).hom := by
    have : Mono ι.hom := inferInstanceAs (Mono Z.ι)
    rw [← sq₁'.isoPullback_hom_snd]
    have := pullback.snd_of_mono (f := ι.hom) (g := φ.totalMap.hom)
    exact mono_comp' (@IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_hom _)) this
  -- the points of the base change of `Z` are exactly the non-smooth points of `X`
  have hrange' : Set.range (Space.pointsMap B integerBase hZ _ (pullback.snd ι φ.totalMap).hom) =
      {x | ¬ Space.IsSmoothAt B integerBase hZ X.toBase.hom x} := by
    ext x
    rw [Set.mem_ofPred_eq, isSmoothAt_iff_hom B hZ φ x,
      show (¬ Space.IsSmoothAt B integerBase hZ Y.toBase.hom
          (Space.pointsMap B integerBase hZ X.total.obj φ.totalMap.hom x)) ↔
        Space.pointsMap B integerBase hZ X.total.obj φ.totalMap.hom x ∈
          Set.range (Space.pointsMap B integerBase hZ Z.toFunctor Z.ι) by rw [hrange]; rfl]
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨_, Space.pointsMap_apply_comm B integerBase hZ sq₁'.w w⟩
    · rintro ⟨z, hz⟩
      obtain ⟨w, -, hw⟩ := Space.exists_points_of_isPullback B integerBase hZ sq₁' z x hz
      exact ⟨w, hw⟩
  ext t
  have h₁ := Space.finite_setOf_pointsMap_eq_iff_of_isPullback B integerBase hZ sq₂ hp
    (Space.isDecentSpace_yoneda B integerBase hZ Y.base)
    (Space.isDecentSpace_yoneda B integerBase hZ X.base) t
  exact ((Space.finite_setOf_pointsMap_comp_eq_iff_of_mono B integerBase hZ Z.ι hrange
    Y.toBase.hom _).symm.trans h₁.symm).trans
      (Space.finite_setOf_pointsMap_comp_eq_iff_of_mono B integerBase hZ _ hrange'
        X.toBase.hom t)

/-- **The open locus of finite singular locus in the base of a family of curves.** For a family
of curves `G` there is an open subspace `W` of its base such that a family of curves `F` mapping
to `G` lies in `Curves⁺` exactly when the morphism of base schemes factors through `W`. -/
theorem exists_isOpenSubspace_finiteNonSmoothLocus (G : CurveFamily B hZ) :
    ∃ W : Subfunctor (schemeSpace G.base).obj,
      Space.IsOpenSubspace B integerBase hZ W ∧
      ∀ (F : CurveFamily B hZ) (a : F ⟶ G),
        IsFiniteNonSmoothLocus B hZ F ↔
          ∃ t : (schemeSpace F.base).obj ⟶ W.toFunctor,
            t ≫ W.ι = (schemeSpaceMap a.baseMap).hom := by
  have hW := Space.isOpenSubspace_openSubspaceOfPoints B integerBase hZ
    (schemeSpace G.base).property _ (isOpen_finiteNonSmoothBaseLocus B hZ G)
  refine ⟨_, hW, fun F a => ?_⟩
  rw [Space.factorsThrough_openSubspace_iff_points B integerBase hZ
      (schemeSpace G.base).property (schemeSpace F.base).property _ hW,
    Space.range_pointsMap_ι_openSubspaceOfPoints,
    isFiniteNonSmoothLocus_iff_finiteNonSmoothBaseLocus_eq_univ,
    ← preimage_finiteNonSmoothBaseLocus B hZ a]
  simp only [Set.range_subset_iff, Set.eq_univ_iff_forall, Set.mem_preimage]

end CurveFamily

end AlgebraicGeometry

end
