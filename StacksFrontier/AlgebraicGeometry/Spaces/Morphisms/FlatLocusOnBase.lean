module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Open
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UnramifiedLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen

/-!
# The open locus on the base over which a base change is flat, or surjective and flat

Consider a commutative triangle of algebraic spaces over a scheme `S`: a morphism `f : X ⟶ Y`
together with morphisms `p : X ⟶ Z` and `q : Y ⟶ Z` such that `f ≫ q = p`.  If `p` is locally
of finite presentation, flat and closed and `q` is locally of finite type, then there is an open
subspace `W` of `Z` through which a morphism `Z' ⟶ Z` factors exactly when the base change of
`f` along it is flat; if moreover `q` is closed, there is one for which it is surjective and
flat.  These are **Stacks 05XB** and **Stacks 05XC**.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.exists_isOpenSubspace_iff_isFlat_baseChange` is **Stacks 05XB**.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_iff_isSurjective_isFlat_baseChange` is
  **Stacks 05XC**.

## Implementation notes

Stacks 05X3, the morphism case of Stacks 05X2, is
`AlgebraicGeometry.Space.flatLocusOpenAndStableUnderBaseChange`; both results below use it
directly, so neither is conditional.

For Stacks 05XB the open subspace is the one cut out, through the correspondence of
Stacks 03BZ, by the complement of the image under `p` of the set of points at which `f` is not
flat: that set is closed by the openness half of Stacks 05X3, and its image is closed because
`p` is.  Factoring through it is the containment of the image of the points of `Z'` in that
complement by Stacks 03IE, while flatness of the base change is flatness at each of its points
by Stacks 03MM; the base-change half of Stacks 05X3 identifies the latter with flatness of `f`
at each point of `X` over a point of the image of `Z'`, and the two agree by a complementation.

For Stacks 05XC the open subspace is the point set of the subspace `W₀` of Stacks 05XB
intersected with the locus of points of `Z` whose fibre in `|Y|` lies in the image of
`X ×_Z W₀ ⟶ Y`.  That locus is open because `q` is closed and because `X ×_Z W₀ ⟶ Y` is open on
points: it factors as the base change of `f` over `W₀` — which is flat by the choice of `W₀`
and locally of finite presentation, so universally open by Stacks 042S — followed by the open
immersion `Y ×_Z W₀ ⟶ Y`.  Over `W₀` that image coincides with the image of `f` itself, and
containment of the image of `Z'` in the latter locus is surjectivity of the base change.

## References

* [Stacks Project, Tag 05XB](https://stacks.math.columbia.edu/tag/05XB)
* [Stacks Project, Tag 05XC](https://stacks.math.columbia.edu/tag/05XC)
* [Stacks Project, Tag 05X3](https://stacks.math.columbia.edu/tag/05X3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### A topological preliminary -/

/-- If `u` is an open map and `v` is a closed map, the set of points of the target of `v` whose
fibre under `v` is contained in the image of `u` is open: it is the complement of the image
under `v` of the closed complement of the open image of `u`. -/
@[ega "IV 15.5.10" "more general"]
private theorem isOpen_setOf_forall_eq_imp_mem_range {P Y Z : Type*} [TopologicalSpace P]
    [TopologicalSpace Y] [TopologicalSpace Z] {u : P → Y} {v : Y → Z}
    (hu : IsOpenMap u) (hv : IsClosedMap v) :
    IsOpen {z | ∀ y, v y = z → y ∈ Set.range u} := by
  have hset : {z | ∀ y, v y = z → y ∈ Set.range u} = (v '' (Set.range u)ᶜ)ᶜ := by
    ext z
    rw [Set.mem_compl_iff, Set.mem_image, Set.mem_ofPred_eq]
    exact ⟨fun h ⟨y, hy, hvy⟩ => hy (h y hvy),
      fun h y hvy => Classical.byContradiction fun hy => h ⟨y, hy, hvy⟩⟩
  rw [hset, isOpen_compl_iff]
  exact hv _ hu.isOpen_range.isClosed_compl

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_flatLocusOnBase :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_flatLocusOnBase
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_flatLocusOnBase B S hS).has_limit _

variable {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The flat locus on the base, Stacks 05XB -/

/-- The image on points of the first projection of a pullback is the preimage of the image of the
second map. -/
private theorem range_pointsMap_pullback_fst {Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : X ⟶ Z) (g : Z' ⟶ Z) :
    Set.range (pointsMap B S hS (pullback p g) (pullback.fst p g)) =
      pointsMap B S hS X p ⁻¹' Set.range (pointsMap B S hS Z' g) := by
  rw [← Set.image_univ, ← Set.image_univ,
    preimage_image_pointsMap_of_isPullback B S hS (IsPullback.of_hasPullback p g).flip Set.univ,
    Set.preimage_univ]

/-- **Stacks 05XB.**  Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S` whose source and target are given over a third algebraic space `Z` by morphisms
`p : X ⟶ Z` and `q : Y ⟶ Z` with `f ≫ q = p`.  If `p` is locally of finite presentation, flat
and closed and `q` is locally of finite type, then there is an open subspace `W` of `Z` through
which a morphism `Z' ⟶ Z` from an algebraic space factors exactly when the base change of `f`
along it is flat.

The open subspace is cut out, through the correspondence of Stacks 03BZ, by the complement of
the image under `p` of the set of points of `X` at which `f` is not flat, which is closed by the
openness half of Stacks 05X3 and whose image is closed because `p` is.  Factoring through it
is the containment of the image of the points of `Z'` in that complement by Stacks 03IE, and
flatness of the base change is flatness at each of its points by Stacks 03MM, which the
base-change half of Stacks 05X3 reads off from flatness of `f` over the image of `Z'`. -/
@[stacks 05XB "the open subspace of the base over which the morphism becomes flat"]
theorem exists_isOpenSubspace_iff_isFlat_baseChange
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (hfq : f ≫ q = p)
    (hp : IsLocallyOfFinitePresentation B S hS p) (hpflat : IsFlat B S hS p)
    (hpc : IsClosedMorphism B S hS p) (hq : IsLocallyOfFiniteType B S hS q) :
    ∃ W : Subfunctor Z, IsOpenSubspace B S hS W ∧
      ∀ (Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Z') (g : Z' ⟶ Z),
        (∃ r : Z' ⟶ W.toFunctor, r ≫ W.ι = g) ↔
          IsFlat B S hS (baseChangeOverBase B S hS f p q hfq g) := by
  obtain ⟨hAopen, hAbc⟩ :=
    flatLocusOpenAndStableUnderBaseChange B S hS hX hY hZ f p q hfq hp hpflat hq
  obtain ⟨W, hWopen, hWrange⟩ := exists_isOpenSubspace_range_pointsMap_eq B S hS hZ
    (pointsMap B S hS X p '' {x : points B S hS X | IsFlatAt B S hS f x}ᶜ)ᶜ
    (hpc _ hAopen.isClosed_compl).isOpen_compl
  refine ⟨W, hWopen, fun Z' hZ' g => ?_⟩
  rw [factorsThrough_openSubspace_iff_points B S hS hZ hZ' W hWopen g, hWrange,
    isFlat_iff_forall_isFlatAt B S hS (baseChangeOverBase B S hS f p q hfq g)]
  constructor
  · intro hsub x'
    rw [hAbc Z' hZ' g x']
    by_contra hbad
    exact hsub ⟨_, rfl⟩ ⟨_, hbad, (pointsMap_apply_comm B S hS
      (IsPullback.of_hasPullback p g).flip.w x').symm⟩
  · rintro hall _ ⟨z', rfl⟩ ⟨x, hxbad, hx⟩
    obtain ⟨x', hx'⟩ : x ∈ Set.range (pointsMap B S hS (pullback p g) (pullback.fst p g)) := by
      rw [range_pointsMap_pullback_fst]
      exact ⟨z', hx.symm⟩
    exact hxbad (hx' ▸ (hAbc Z' hZ' g x').mp (hall x'))

/-! ### Surjectivity of a base change, read on the fibres of `q` -/

/-- **Surjectivity of a base change of `f` over `Z`, read on the fibres of `q`.** The base
change of `f` along `g : Z' ⟶ Z` is surjective exactly when every point of `|Y|` lying over a
point of the image of `g` lies in the image of `f`.

Both directions move points across the cartesian square exhibiting the base change as a base
change of `f`, by Stacks 03H4. -/
theorem isSurjective_baseChangeOverBase_iff (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z)
    (hfq : f ≫ q = p) {Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Z' ⟶ Z) :
    IsSurjective B S hS (baseChangeOverBase B S hS f p q hfq g) ↔
      Set.range (pointsMap B S hS Z' g) ⊆
        {z | ∀ y, pointsMap B S hS Y q y = z → y ∈ Set.range (pointsMap B S hS X f)} := by
  have hbc : IsPullback (pullback.fst p g) (baseChangeOverBase B S hS f p q hfq g) f
      (pullback.fst q g) := isPullback_baseChangeOverBase B S hS f p q hfq g
  constructor
  · rintro hsurj z ⟨z', rfl⟩ y hy
    obtain ⟨t, ht₁, -⟩ := exists_points_of_isPullback B S hS
      (IsPullback.of_hasPullback q g) y z' hy
    obtain ⟨w, hw⟩ := hsurj t
    refine ⟨pointsMap B S hS (pullback p g) (pullback.fst p g) w, ?_⟩
    rw [pointsMap_apply_comm B S hS hbc.w w, hw, ht₁]
  · intro hsub t
    have hcompat : pointsMap B S hS Y q
        (pointsMap B S hS (pullback q g) (pullback.fst q g) t) =
        pointsMap B S hS Z' g
          (pointsMap B S hS (pullback q g) (pullback.snd q g) t) :=
      pointsMap_apply_comm B S hS (pullback.condition (f := q) (g := g)) t
    obtain ⟨x, hx⟩ := hsub ⟨_, rfl⟩ _ hcompat
    obtain ⟨w, -, hw⟩ := exists_points_of_isPullback B S hS hbc x t hx
    exact ⟨w, hw⟩

/-! ### The surjective and flat locus on the base, Stacks 05XC -/

/-- **Stacks 05XC.**  Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S` whose source and target are given over a third algebraic space `Z` by morphisms
`p : X ⟶ Z` and `q : Y ⟶ Z` with `f ≫ q = p`.  If `p` is locally of finite presentation, flat
and closed and `q` is locally of finite type and closed, then there is an open subspace `W` of
`Z` through which a morphism `Z' ⟶ Z` from an algebraic space factors exactly when the base
change of `f` along it is surjective and flat.

The open subspace is cut out by the point set of the subspace `W₀` of Stacks 05XB intersected
with the locus of points of `Z` whose fibre in `|Y|` lies in the image of `X ×_Z W₀ ⟶ Y`.  That
locus is open because `q` is closed and because `X ×_Z W₀ ⟶ Y` is open on points, being the
base change of `f` over `W₀` — flat by the choice of `W₀` and locally of finite presentation,
hence universally open by Stacks 042S — followed by the open immersion `Y ×_Z W₀ ⟶ Y`.  Over
`W₀` its image coincides with the image of `f`, and containment of the image of `Z'` in the
locus is surjectivity of the base change. -/
@[stacks 05XC "the open subspace of the base over which the morphism becomes surjective and flat"]
theorem exists_isOpenSubspace_iff_isSurjective_isFlat_baseChange
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (hfq : f ≫ q = p)
    (hp : IsLocallyOfFinitePresentation B S hS p) (hpflat : IsFlat B S hS p)
    (hpc : IsClosedMorphism B S hS p) (hq : IsLocallyOfFiniteType B S hS q)
    (hqc : IsClosedMorphism B S hS q) :
    ∃ W : Subfunctor Z, IsOpenSubspace B S hS W ∧
      ∀ (Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Z') (g : Z' ⟶ Z),
        (∃ r : Z' ⟶ W.toFunctor, r ≫ W.ι = g) ↔
          IsSurjective B S hS (baseChangeOverBase B S hS f p q hfq g) ∧
            IsFlat B S hS (baseChangeOverBase B S hS f p q hfq g) := by
  have hf : IsLocallyOfFinitePresentation B S hS f :=
    isLocallyOfFinitePresentation_of_comp B S hS hX hY hZ f q (by rwa [hfq]) hq
  obtain ⟨W₀, hW₀, hW₀flat⟩ := exists_isOpenSubspace_iff_isFlat_baseChange B S hS hX hY hZ
    f p q hfq hp hpflat hpc hq
  set fW := baseChangeOverBase B S hS f p q hfq W₀.ι
  have hPX : IsAlgebraicSpace B S hS (pullback p W₀.ι) :=
    isAlgebraicSpace_pullback B S hS p W₀.ι hX hW₀.1 hZ
  have hPY : IsAlgebraicSpace B S hS (pullback q W₀.ι) :=
    isAlgebraicSpace_pullback B S hS q W₀.ι hY hW₀.1 hZ
  have hbcW : IsPullback (pullback.fst p W₀.ι) fW f (pullback.fst q W₀.ι) :=
    isPullback_baseChangeOverBase B S hS f p q hfq W₀.ι
  have hιetale := presheaf_etale_of_isOpenImmersion B S hS hW₀.2
  have hπQetale := presheaf_of_isPullback B S hS
    (IsPullback.of_hasPullback q W₀.ι).flip hιetale
  have hfWflat : IsFlat B S hS fW :=
    (hW₀flat W₀.toFunctor hW₀.1 W₀.ι).mp ⟨𝟙 _, Category.id_comp _⟩
  have hfWfp : IsLocallyOfFinitePresentation B S hS fW :=
    holdsOnEveryEtaleChart_of_isPullback B S hS hbcW.flip hπQetale hf
  have hfWopen : IsOpenMorphism B S hS fW :=
    isOpen_of_universallyOpen B S hS hPY fW
      (universallyOpen_of_isFlat_of_isLocallyOfFinitePresentation B S hS hPX hPY fW
        hfWflat hfWfp)
  have hcompOpen : IsOpenMap
      (pointsMap B S hS (pullback p W₀.ι) (pullback.fst p W₀.ι ≫ f)) := by
    rw [hbcW.w, pointsMap_comp]
    exact (isOpenMap_pointsMap_of_presheafEtale B S hS (pullback.fst q W₀.ι) hπQetale).comp
      hfWopen
  set A : Set (points B S hS Z) := {z | ∀ y, pointsMap B S hS Y q y = z →
    y ∈ Set.range (pointsMap B S hS (pullback p W₀.ι) (pullback.fst p W₀.ι ≫ f))}
  have hAopen : IsOpen A := isOpen_setOf_forall_eq_imp_mem_range hcompOpen hqc
  set R₀ := Set.range (pointsMap B S hS W₀.toFunctor W₀.ι)
  obtain ⟨W, hWopen, hWrange⟩ := exists_isOpenSubspace_range_pointsMap_eq B S hS hZ (A ∩ R₀)
    (hAopen.inter (isOpen_range_pointsMap_of_isOpenImmersion B S hS W₀.ι hW₀.2))
  have hfibreEq : ∀ z ∈ R₀, z ∈ A ↔
      ∀ y, pointsMap B S hS Y q y = z → y ∈ Set.range (pointsMap B S hS X f) := by
    intro z hz
    refine ⟨fun h y hy => ?_, fun h y hy => ?_⟩
    · obtain ⟨u, hu⟩ := h y hy
      exact ⟨pointsMap B S hS (pullback p W₀.ι) (pullback.fst p W₀.ι) u, by
        rw [← pointsMap_comp_apply, hu]⟩
    · obtain ⟨x, hx⟩ := h y hy
      obtain ⟨u, hu⟩ : x ∈ Set.range
          (pointsMap B S hS (pullback p W₀.ι) (pullback.fst p W₀.ι)) := by
        rw [range_pointsMap_pullback_fst, Set.mem_preimage, ← hfq, pointsMap_comp_apply, hx, hy]
        exact hz
      exact ⟨u, by rw [pointsMap_comp_apply, hu, hx]⟩
  refine ⟨W, hWopen, fun Z' hZ' g => ?_⟩
  rw [factorsThrough_openSubspace_iff_points B S hS hZ hZ' W hWopen g, hWrange,
    Set.subset_inter_iff]
  have hflat := hW₀flat Z' hZ' g
  have hW₀pts := factorsThrough_openSubspace_iff_points B S hS hZ hZ' W₀ hW₀ g
  have hsurj := isSurjective_baseChangeOverBase_iff B S hS f p q hfq g
  constructor
  · rintro ⟨hA, hR⟩
    exact ⟨hsurj.mpr fun z hz => (hfibreEq z (hR hz)).mp (hA hz),
      hflat.mp (hW₀pts.mpr hR)⟩
  · rintro ⟨hs, hfl⟩
    have hR : Set.range (pointsMap B S hS Z' g) ⊆ R₀ := hW₀pts.mp (hflat.mpr hfl)
    exact ⟨fun z hz => (hfibreEq z (hR hz)).mpr (hsurj.mp hs hz), hR⟩

end AlgebraicGeometry.Space

end
