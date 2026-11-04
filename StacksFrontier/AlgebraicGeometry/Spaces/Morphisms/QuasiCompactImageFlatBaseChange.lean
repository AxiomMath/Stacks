module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImageSiteOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SchemeImageDominant
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae03KM
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flat base change of the scheme-theoretic image of a quasi-compact morphism

Let `f : X ⟶ Y` be a flat morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B` and let `g : V ⟶ Y` be a quasi-compact morphism of algebraic spaces.  Write
`Z ⊆ Y` for the scheme-theoretic image of Stacks 082X of `g` and `Z' ⊆ X` for the
scheme-theoretic image of the base change `V ×_Y X ⟶ X`.  Stacks 089E asserts that
`Z' = f⁻¹(Z)`.

## Main results

* `AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_pullback_snd_yoneda_of_flat`: for a
  flat morphism of the big fppf category over `S` and a quasi-compact one with the same target,
  the scheme-theoretic image of the base change is the inverse image of the scheme-theoretic
  image.
* `AlgebraicGeometry.Space.range_subset_closure_range_of_mem_schemeTheoreticImageSubfunctor`:
  a section of the scheme-theoretic image of a quasi-compact morphism of the site lies over the
  closure of the image of the underlying morphism of schemes.
* `AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_pullback_snd_of_isFlat_of_isQuasiCompact`
  states that the scheme-theoretic image of a quasi-compact morphism of algebraic spaces over `S`
  commutes with flat base change.  The primed variant of that name states the same for morphisms of
  presheaves carrying algebraicity hypotheses.

## References

* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03MM](https://stacks.math.columbia.edu/tag/03MM)
* [Stacks Project, Tag 081I](https://stacks.math.columbia.edu/tag/081I)
* [Stacks Project, Tag 082X](https://stacks.math.columbia.edu/tag/082X)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
* [Stacks Project, Tag 089E](https://stacks.math.columbia.edu/tag/089E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)


/-- A factorization through a morphism of the site, given on the underlying schemes, comes
from a factorization in the site itself. -/
private lemma exists_hom_of_scheme_hom_comp {T R V : BigFppfOver B S hS} (j : R ⟶ V) (g : T ⟶ V)
    (k : (BigFppfOver.toScheme B S hS).obj T ⟶ (BigFppfOver.toScheme B S hS).obj R)
    (hk : k ≫ (BigFppfOver.toScheme B S hS).map j = (BigFppfOver.toScheme B S hS).map g) :
    ∃ l : T ⟶ R, l ≫ j = g := by
  have hk₀ : B.inclusion.preimage k ≫ j.left = g.left := by
    refine B.inclusion.map_injective ?_
    rwa [B.inclusion.map_comp, B.inclusion.map_preimage k]
  exact ⟨Over.homMk (B.inclusion.preimage k)
    (by rw [← j.w, ← Category.assoc, hk₀, g.w]), Over.OverMorphism.ext hk₀⟩

/-- The scheme-theoretic image of the morphism of schemes underlying a morphism of the site is
again an object of the site: it is a closed subscheme of the target, hence no larger, and it
carries a closed immersion to the target with the same kernel ideal sheaf as the morphism. -/
private lemma exists_schemeImage_site' {A V : BigFppfOver B S hS} (f : A ⟶ V) :
    ∃ (R : BigFppfOver B S hS) (q : R ⟶ V) (l : A ⟶ R),
      AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map q) ∧
      ((BigFppfOver.toScheme B S hS).map q).ker =
        ((BigFppfOver.toScheme B S hS).map f).ker ∧ l ≫ q = f := by
  classical
  have hI : B.Contains ((BigFppfOver.toScheme B S hS).map f).image :=
    lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact
      ((BigFppfOver.toScheme B S hS).map f).imageι) V.left.property
  let qI : B.obj hI ⟶ V.left := B.inclusion.preimage (X := B.obj hI) (Y := V.left)
    ((BigFppfOver.toScheme B S hS).map f).imageι
  let lI : A.left ⟶ B.obj hI := B.inclusion.preimage (X := A.left) (Y := B.obj hI)
    ((BigFppfOver.toScheme B S hS).map f).toImage
  have hqI : B.inclusion.map qI = ((BigFppfOver.toScheme B S hS).map f).imageι :=
    B.inclusion.map_preimage (X := B.obj hI) (Y := V.left)
      ((BigFppfOver.toScheme B S hS).map f).imageι
  have hlI : lI ≫ qI = f.left := by
    refine B.inclusion.map_injective ?_
    rw [B.inclusion.map_comp, B.inclusion.map_preimage (X := A.left) (Y := B.obj hI)
      ((BigFppfOver.toScheme B S hS).map f).toImage, hqI]
    show ((BigFppfOver.toScheme B S hS).map f).toImage ≫
      ((BigFppfOver.toScheme B S hS).map f).imageι = (BigFppfOver.toScheme B S hS).map f
    rw [Scheme.Hom.toImage_imageι]
  refine ⟨Over.mk (qI ≫ V.hom), Over.homMk qI, Over.homMk lI (by
    show lI ≫ (qI ≫ V.hom) = A.hom
    rw [← Category.assoc, hlI, f.w]), ?_, ?_, ?_⟩
  · show AlgebraicGeometry.IsClosedImmersion (B.inclusion.map qI)
    rw [hqI]; infer_instance
  · show (B.inclusion.map qI).ker = _
    rw [hqI, Scheme.Hom.imageι, Scheme.IdealSheafData.ker_subschemeι]
  · ext
    exact congrArg (fun k => k.hom) hlI

/-- The scheme-theoretic image of a represented morphism lies in the range of a represented closed
immersion through which the morphism factors. -/
private lemma schemeTheoreticImageSubfunctor_le_range_of_comp_eq {A R V : BigFppfOver B S hS}
    (q : R ⟶ V) (l : A ⟶ R) (g : A ⟶ V)
    (hq : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map q))
    (hlq : l ≫ q = g) :
    schemeTheoreticImageSubfunctor B S hS (yoneda.map g) ≤ Subfunctor.range (yoneda.map q) := by
  refine schemeTheoreticImageSubfunctor_le B S hS (yoneda.map g)
    (isClosedSubspace_range_yoneda_map B S hS q hq) ?_
  rw [← hlq, yoneda.map_comp]
  exact Subfunctor.range_comp_le _ _

/-- Let `g : A ⟶ V` be a morphism of the site whose underlying morphism of schemes is
quasi-compact, and let `s : T ⟶ V` be a section over `T` of the scheme-theoretic image of
`yoneda.map g`. Then the image of the morphism of schemes underlying `s` lies in the closure of
the image of the one underlying `g`. -/
theorem range_subset_closure_range_of_mem_schemeTheoreticImageSubfunctor
    {A V T : BigFppfOver B S hS} (g : A ⟶ V)
    [AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map g)] {s : T ⟶ V}
    (hs : s ∈ (schemeTheoreticImageSubfunctor B S hS (yoneda.map g)).obj (op T)) :
    Set.range ((BigFppfOver.toScheme B S hS).map s) ⊆
      closure (Set.range ((BigFppfOver.toScheme B S hS).map g)) := by
  obtain ⟨R, q, l, hq, hqker, hlq⟩ := exists_schemeImage_site' B S hS g
  obtain ⟨m, hm⟩ :=
    schemeTheoreticImageSubfunctor_le_range_of_comp_eq B S hS q l g hq hlq _ hs
  change m ≫ q = s at hm
  rintro _ ⟨t, rfl⟩
  rw [← Scheme.Hom.support_ker, ← hqker, Scheme.Hom.support_ker, ← hm, Functor.map_comp,
    Scheme.Hom.comp_apply]
  exact subset_closure ⟨_, rfl⟩

/-- A represented morphism factors through a represented closed immersion exactly when the
kernel ideal sheaf of that closed immersion is contained in the kernel ideal sheaf of the
morphism. -/
private lemma range_yoneda_le_iff_ker_le' {T R V : BigFppfOver B S hS} (j : R ⟶ V) (g : T ⟶ V)
    [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)] :
    Subfunctor.range (yoneda.map g) ≤ Subfunctor.range (yoneda.map j) ↔
      ((BigFppfOver.toScheme B S hS).map j).ker ≤
        ((BigFppfOver.toScheme B S hS).map g).ker := by
  constructor
  · intro h
    obtain ⟨l, hl⟩ := h (op T) (show g ∈
      (Subfunctor.range (yoneda.map g)).obj (op T) from ⟨𝟙 T, by simp⟩)
    change l ≫ j = g at hl
    rw [← hl, (BigFppfOver.toScheme B S hS).map_comp]
    exact Scheme.Hom.le_ker_comp _ _
  · intro h
    obtain ⟨l, hl⟩ := exists_hom_of_scheme_hom_comp B S hS j g
      (IsClosedImmersion.lift ((BigFppfOver.toScheme B S hS).map j)
        ((BigFppfOver.toScheme B S hS).map g) h)
      (IsClosedImmersion.lift_fac _ _ h)
    rw [← hl, yoneda.map_comp]
    exact Subfunctor.range_comp_le _ _

/-- Two represented closed immersions have the same range exactly when they have the same kernel
ideal sheaf. -/
private lemma range_yoneda_eq_iff_ker_eq {R T V : BigFppfOver B S hS} (j : R ⟶ V) (k : T ⟶ V)
    [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)]
    [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map k)] :
    Subfunctor.range (yoneda.map j) = Subfunctor.range (yoneda.map k) ↔
      ((BigFppfOver.toScheme B S hS).map j).ker = ((BigFppfOver.toScheme B S hS).map k).ker := by
  rw [le_antisymm_iff, le_antisymm_iff, range_yoneda_le_iff_ker_le',
    range_yoneda_le_iff_ker_le', and_comm]

/-- A represented closed immersion whose range is the scheme-theoretic image of a represented
morphism has the same kernel ideal sheaf as that morphism. -/
private lemma ker_eq_of_schemeTheoreticImage_eq_range {T R V : BigFppfOver B S hS}
    (g : T ⟶ V) (j : R ⟶ V)
    [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)]
    (hj : schemeTheoreticImageSubfunctor B S hS (yoneda.map g) =
      Subfunctor.range (yoneda.map j)) :
    ((BigFppfOver.toScheme B S hS).map j).ker = ((BigFppfOver.toScheme B S hS).map g).ker := by
  refine le_antisymm ((range_yoneda_le_iff_ker_le' B S hS j g).1 ?_) ?_
  · rw [← hj]
    exact range_le_schemeTheoreticImageSubfunctor B S hS (yoneda.map g)
  · obtain ⟨R', q, l, hq, hqker, hlq⟩ := exists_schemeImage_site' B S hS g
    have := (range_yoneda_le_iff_ker_le' B S hS q j).1
      (hj ▸ schemeTheoreticImageSubfunctor_le_range_of_comp_eq B S hS q l g hq hlq)
    rwa [hqker] at this

/-- In a cartesian square of presheaves of types, the inverse image of the range of one side
along the opposite side is the range of the parallel projection. -/
private lemma range_preimage_eq_of_isPullback {C : Type*} [Category C]
    {A R X Y : Cᵒᵖ ⥤ Type u} {a : A ⟶ R} {b : A ⟶ X} {j : R ⟶ Y} {f : X ⟶ Y}
    (h : IsPullback a b j f) :
    (Subfunctor.range j).preimage f = Subfunctor.range b := by
  ext U x
  exact Set.ext_iff.mp (Types.range_snd_of_isPullback
    (h.map ((evaluation Cᵒᵖ (Type u)).obj U))).symm x

/-- The kernel ideal sheaf of a base change of a represented closed immersion is the inverse
image of its kernel ideal sheaf. -/
private lemma ker_pullback_snd_of_isClosedImmersion {R X Y : BigFppfOver B S hS}
    (j : R ⟶ Y) (f : X ⟶ Y)
    [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)] :
    ((BigFppfOver.toScheme B S hS).map (pullback.snd j f)).ker =
      ((BigFppfOver.toScheme B S hS).map j).ker.comap
        ((BigFppfOver.toScheme B S hS).map f) := by
  have sq := ((IsPullback.of_hasPullback j f).map (BigFppfOver.toScheme B S hS)).flip
  rw [← sq.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

/-- The base change of a represented closed immersion is a closed immersion. -/
private lemma isClosedImmersion_map_pullback_snd {R X Y : BigFppfOver B S hS}
    (j : R ⟶ Y) (f : X ⟶ Y)
    [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)] :
    AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (pullback.snd j f)) :=
  AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange.of_isPullback
    ((IsPullback.of_hasPullback j f).map (BigFppfOver.toScheme B S hS)) ‹_›

/-- For a flat morphism `f` of the big fppf category over `S` and a quasi-compact morphism `g`
of the site with the same target, the scheme-theoretic image of the base change of `g` along
`f` is the inverse image along `f` of the scheme-theoretic image of `g`. -/
@[ega "IV 2.3.2" "more general"]
theorem schemeTheoreticImageSubfunctor_pullback_snd_yoneda_of_flat
    {X Y V : BigFppfOver B S hS} (f : X ⟶ Y) (g : V ⟶ Y)
    [AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map f)]
    [AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map g)] :
    schemeTheoreticImageSubfunctor B S hS (yoneda.map (pullback.snd g f)) =
      (schemeTheoreticImageSubfunctor B S hS (yoneda.map g)).preimage (yoneda.map f) := by
  obtain ⟨R, j, hj, hI⟩ := exists_closedImmersion_range B S hS
    (schemeTheoreticImageSubfunctor B S hS (yoneda.map g))
    (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS _
      (isAlgebraicSpace_yoneda B S hS Y))
  obtain ⟨T, k, hk, hJ⟩ := exists_closedImmersion_range B S hS
    (schemeTheoreticImageSubfunctor B S hS (yoneda.map (pullback.snd g f)))
    (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS _
      (isAlgebraicSpace_yoneda B S hS X))
  have hjker := ker_eq_of_schemeTheoreticImage_eq_range B S hS g j hI
  have hkker := ker_eq_of_schemeTheoreticImage_eq_range B S hS (pullback.snd g f) k hJ
  have sqg := (IsPullback.of_hasPullback g f).map (BigFppfOver.toScheme B S hS)
  have := isClosedImmersion_map_pullback_snd B S hS j f
  have heq : ((BigFppfOver.toScheme B S hS).map k).ker =
      ((BigFppfOver.toScheme B S hS).map (pullback.snd j f)).ker := by
    rw [hkker, ← sqg.isoPullback_hom_snd, Scheme.Hom.ker_comp_of_isIso,
      AlgebraicGeometry.ker_pullback_snd_eq_comap, ker_pullback_snd_of_isClosedImmersion, hjker]
  rw [hJ, hI, range_preimage_eq_of_isPullback ((IsPullback.of_hasPullback j f).map yoneda)]
  exact (range_yoneda_eq_iff_ker_eq B S hS _ _).2 heq

/-- If the range of a composite lies in a subfunctor which is a sheaf and the first factor is
locally surjective, the range of the second factor lies in it as well. -/
private theorem range_le_of_comp_locallySurjective {C : Type*} [Category C]
    (J : GrothendieckTopology C) {F G H : Cᵒᵖ ⥤ Type u}
    (q : G ⟶ F) (f : F ⟶ H) (A : Subfunctor H)
    (hH : Presheaf.IsSheaf J H) (hA : Presheaf.IsSheaf J A.toFunctor)
    (hq : Presheaf.IsLocallySurjective J q)
    (hcomp : Subfunctor.range (q ≫ f) ≤ A) :
    Subfunctor.range f ≤ A := by
  intro U x hx
  obtain ⟨z, hz⟩ := hx
  rw [← hz]
  refine (A.isSheaf_iff ((isSheaf_iff_isSheaf_of_type J H).mp hH)).1
    ((isSheaf_iff_isSheaf_of_type J A.toFunctor).mp hA) U (f.app U z) ?_
  refine J.superset_covering ?_ (Presheaf.imageSieve_mem J q z)
  rintro V k ⟨y, hy⟩
  have hn : H.map k.op (f.app U z) = f.app (op V) (F.map k.op z) :=
    (congrArg (fun m => m z) (f.naturality k.op)).symm
  show H.map k.op (f.app U z) ∈ A.obj (op V)
  rw [hn, ← hy]
  exact hcomp (op V) ⟨y, rfl⟩

/-- Containment of subfunctors of a sheaf may be tested after inverse image along a locally
surjective morphism, provided the larger subfunctor is a sheaf. -/
private theorem subfunctor_le_of_preimage_le_of_locallySurjective {D : Type*} [Category D]
    (J : GrothendieckTopology D) {F G : Dᵒᵖ ⥤ Type u}
    (e : G ⟶ F) (A C : Subfunctor F)
    (hF : Presheaf.IsSheaf J F) (hC : Presheaf.IsSheaf J C.toFunctor)
    (he : Presheaf.IsLocallySurjective J e)
    (hAC : A.preimage e ≤ C.preimage e) : A ≤ C := by
  intro U x hx
  refine (C.isSheaf_iff ((isSheaf_iff_isSheaf_of_type J F).mp hF)).1
    ((isSheaf_iff_isSheaf_of_type J C.toFunctor).mp hC) U x ?_
  refine J.superset_covering ?_ (Presheaf.imageSieve_mem J e x)
  rintro V k ⟨y, hy⟩
  have hxy : e.app (op V) y = F.map k.op x := hy
  have hyA : y ∈ (A.preimage e).obj (op V) := by
    show e.app (op V) y ∈ A.obj (op V)
    rw [hxy]; exact A.map k.op hx
  have hyC := hAC (op V) hyA
  change e.app (op V) y ∈ C.obj (op V) at hyC
  rwa [hxy] at hyC

/-- Local surjectivity of a morphism of presheaves is stable under base change. -/
private theorem locallySurjective_of_isPullback {C : Type*} [Category C]
    (J : GrothendieckTopology C) {A D X Y : Cᵒᵖ ⥤ Type u}
    {a : A ⟶ D} {b : A ⟶ X} {g : D ⟶ Y} {f : X ⟶ Y}
    (sq : IsPullback a b g f) (hg : Presheaf.IsLocallySurjective J g) :
    Presheaf.IsLocallySurjective J b := by
  refine ⟨fun {U} x => J.superset_covering ?_ (Presheaf.imageSieve_mem J g (f.app _ x))⟩
  rintro T k ⟨y, hy⟩
  have hxy : g.app _ y = f.app _ (X.map k.op x) := by
    rw [hy]; exact congrArg (fun t => t x) (f.naturality k.op).symm
  obtain ⟨z, _, hz'⟩ := Types.exists_of_isPullback (sq.app (op T)) y (X.map k.op x) hxy
  exact ⟨z, hz'⟩

/-- Precomposition with a locally surjective morphism does not change the scheme-theoretic
image. -/
private lemma schemeTheoreticImageSubfunctor_precomp_locallySurjective
    {W V Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (w : W ⟶ V) (g : V ⟶ Y)
    (hw : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) w) :
    schemeTheoreticImageSubfunctor B S hS (w ≫ g) =
      schemeTheoreticImageSubfunctor B S hS g := by
  refine le_antisymm (schemeTheoreticImageSubfunctor_le B S hS _
    (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS g hY)
    ((Subfunctor.range_comp_le _ _).trans
      (range_le_schemeTheoreticImageSubfunctor B S hS g))) ?_
  refine schemeTheoreticImageSubfunctor_le B S hS g
    (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS (w ≫ g) hY) ?_
  exact range_le_of_comp_locallySurjective (BigFppfOver.topology B S hS) w g _ hY.isSheaf
    (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS (w ≫ g) hY).1.isSheaf hw
    (range_le_schemeTheoreticImageSubfunctor B S hS (w ≫ g))

/-- The inclusion of an open subscheme of an object of the big fppf category over `S`. -/
private noncomputable abbrev siteOpenObjectι (V : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj V).Opens) : siteOpenObject B S hS V W ⟶ V :=
  Over.homMk (B.inclusion.preimage
    (X := B.obj ((Scheme.size_coe_opens_le _ W).trans_lt V.left.property))
    (Y := V.left) W.ι) (by rfl)

/-- The morphism of schemes underlying the inclusion of an open subscheme of an object of the
site is the inclusion of that open. -/
private lemma siteOpenObjectι_map (V : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj V).Opens) :
    (BigFppfOver.toScheme B S hS).map (siteOpenObjectι B S hS V W) = W.ι :=
  B.inclusion.map_preimage
    (X := B.obj ((Scheme.size_coe_opens_le _ W).trans_lt V.left.property)) (Y := V.left) W.ι

/-- Two closed subspaces of a representable presheaf whose inverse images along the opens of
an affine open cover agree are equal. -/
private lemma closedSubspace_eq_of_affineOpen_cover (U : BigFppfOver B S hS)
    (A C : Subfunctor (yoneda.obj U)) (hA : IsClosedSubspace B S hS A)
    (hC : IsClosedSubspace B S hS C)
    {ι : Type*} (O : ι → ((BigFppfOver.toScheme B S hS).obj U).affineOpens)
    (hO : ⨆ i, (O i).1 = ⊤)
    (h : ∀ i, A.preimage (yoneda.map (siteOpenObjectι B S hS U (O i).1)) =
      C.preimage (yoneda.map (siteOpenObjectι B S hS U (O i).1))) : A = C := by
  obtain ⟨R, j, hj, rfl⟩ := exists_closedImmersion_range B S hS A hA
  obtain ⟨T, k, hk, rfl⟩ := exists_closedImmersion_range B S hS C hC
  have heq : ((BigFppfOver.toScheme B S hS).map j).ker =
      ((BigFppfOver.toScheme B S hS).map k).ker := by
    refine Scheme.IdealSheafData.ext_of_iSup_eq_top O hO ?_
    intro n
    set W := O n with hW
    have hmap : (BigFppfOver.toScheme B S hS).map (siteOpenObjectι B S hS U W.1) = W.1.ι :=
      siteOpenObjectι_map B S hS U W.1
    have := isClosedImmersion_map_pullback_snd B S hS j (siteOpenObjectι B S hS U W.1)
    have := isClosedImmersion_map_pullback_snd B S hS k (siteOpenObjectι B S hS U W.1)
    have hr := h n
    rw [range_preimage_eq_of_isPullback
        ((IsPullback.of_hasPullback j (siteOpenObjectι B S hS U W.1)).map yoneda),
      range_preimage_eq_of_isPullback
        ((IsPullback.of_hasPullback k (siteOpenObjectι B S hS U W.1)).map yoneda)] at hr
    have he : ((BigFppfOver.toScheme B S hS).map
          (pullback.snd j (siteOpenObjectι B S hS U W.1))).ker =
        ((BigFppfOver.toScheme B S hS).map
          (pullback.snd k (siteOpenObjectι B S hS U W.1))).ker :=
      (range_yoneda_eq_iff_ker_eq B S hS _ _).mp hr
    rw [ker_pullback_snd_of_isClosedImmersion, ker_pullback_snd_of_isClosedImmersion,
      hmap] at he
    have : IsAffine W.1.toScheme := W.2
    have he' := congrArg
      (fun I : W.1.toScheme.IdealSheafData => I.ideal ⟨⊤, isAffineOpen_top _⟩) he
    have he'' := (Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion
      ((BigFppfOver.toScheme B S hS).map j).ker W.1.ι ⟨⊤, isAffineOpen_top _⟩).symm.trans
        (he'.trans (Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion
          ((BigFppfOver.toScheme B S hS).map k).ker W.1.ι ⟨⊤, isAffineOpen_top _⟩))
    have he3 := Ideal.comap_injective_of_surjective _
      (ConcreteCategory.bijective_of_isIso (W.1.ι.appIso ⊤).inv).2 he''
    have hW' : (⟨W.1.ι ''ᵁ (⊤ : W.1.toScheme.Opens),
        (isAffineOpen_top _).image_of_isOpenImmersion W.1.ι⟩ :
        ((BigFppfOver.toScheme B S hS).obj U).affineOpens) = W := Subtype.ext (by simp)
    exact (congrArg (fun Q => ((BigFppfOver.toScheme B S hS).map j).ker.ideal Q =
      ((BigFppfOver.toScheme B S hS).map k).ker.ideal Q) hW').mp he3
  exact (range_yoneda_eq_iff_ker_eq B S hS _ _).mpr heq


/-- A morphism of the site which is étale on underlying schemes represents a relatively
representable étale morphism of presheaves. -/
private lemma presheafEtale_yoneda_map {U V : BigFppfOver B S hS} (f : U ⟶ V)
    (hf : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map f)) :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map f) :=
  (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
    (@AlgebraicGeometry.Etale.{u}) f).2 hf

/-- An étale morphism out of a representable presheaf is relatively representable étale. -/
private lemma presheafEtale_of_isEtale {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : BigFppfOver B S hS} (a : yoneda.obj T ⟶ G) (ha : IsEtale B S hS a) :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a := by
  have hid := presheafEtale_yoneda_map B S hS (𝟙 T) (by
    rw [(BigFppfOver.toScheme B S hS).map_id]; infer_instance)
  simpa using ha T (𝟙 _) (by simpa using hid)

/-- The composite of the inclusion of an open subscheme with an étale morphism out of a
representable presheaf is relatively representable étale. -/
private lemma presheafEtale_siteOpenObjectι_comp {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : BigFppfOver B S hS} (W : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (a : yoneda.obj T ⟶ G) (ha : IsEtale B S hS a) :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (siteOpenObjectι B S hS T W) ≫ a) :=
  presheafEtale_comp B S hS
    (presheafEtale_yoneda_map B S hS _ (by rw [siteOpenObjectι_map]; infer_instance))
    (presheafEtale_of_isEtale B S hS a ha)

/-- A morphism of sheaves on the big fppf site which is surjective and étale after every
represented base change is locally surjective. -/
private theorem locallySurjective_of_presheaf_surjective_etale
    {G F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : G ⟶ F)
    (haS : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (haE : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) a := by
  have hflat : (MorphismProperty.inverseImage
      ((fun _ _ f => AlgebraicGeometry.Flat f ∧
        AlgebraicGeometry.LocallyOfFinitePresentation f ∧
        AlgebraicGeometry.Surjective f) : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a := by
    refine ⟨haE.1, ?_⟩
    intro V W g fst snd hpb
    have : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map snd) :=
      haE.2 g fst snd hpb
    exact ⟨inferInstance, inferInstance, haS.2 g fst snd hpb⟩
  exact isLocallySurjective_of_representable_flat_locallyOfFinitePresentation_surjective
    B S hS (⟨a⟩ : (⟨G, hG⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ ⟨F, hF⟩) hflat

/-- In any cartesian square, the scheme-theoretic image of the base change of a quasi-compact
morphism along an étale morphism is the inverse image of its scheme-theoretic image. -/
@[ega "IV 2.3.2" "special case"]
private lemma schemeTheoreticImageSubfunctor_of_isPullback_of_isEtale
    {A D X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hD : IsAlgebraicSpace B S hS D) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    {a : A ⟶ D} {b : A ⟶ X} {g : D ⟶ Y} {f : X ⟶ Y}
    (sq : IsPullback a b g f) (hg : IsQuasiCompact B S hS g) (hf : IsEtale B S hS f) :
    schemeTheoreticImageSubfunctor B S hS b =
      (schemeTheoreticImageSubfunctor B S hS g).preimage f := by
  rw [← schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale_of_isQuasiCompact'
    B S hS g f hD hY hX hg hf]
  refine schemeTheoreticImageSubfunctor_congr_range B S hS b (pullback.snd g f) hX ?_
  rw [← range_preimage_eq_of_isPullback sq,
    ← range_preimage_eq_of_isPullback (IsPullback.of_hasPullback g f)]

/-- For a flat morphism `f` of the site with affine target and a quasi-compact morphism `g`
from an algebraic space to that target, the scheme-theoretic image of a base change of `g` along
`f` is the inverse image of the scheme-theoretic image of `g`. -/
@[ega "IV 2.3.2" "special case"]
private lemma schemeTheoreticImageSubfunctor_of_isPullback_of_flat_isAffine
    {X Y : BigFppfOver B S hS} {A V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hV : IsAlgebraicSpace B S hS V) (f : X ⟶ Y) (g : V ⟶ yoneda.obj Y)
    [AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map f)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Y)]
    (hg : IsQuasiCompact B S hS g)
    {a : A ⟶ V} {b : A ⟶ yoneda.obj X} (sq : IsPullback a b g (yoneda.map f)) :
    schemeTheoreticImageSubfunctor B S hS b =
      (schemeTheoreticImageSubfunctor B S hS g).preimage (yoneda.map f) := by
  have hY := isAlgebraicSpace_yoneda B S hS Y
  have hX := isAlgebraicSpace_yoneda B S hS X
  have hVqc : IsQuasiCompactSpace B S hS V :=
    isQuasiCompactSpace_of_iso B S hS (asIso (pullback.snd (𝟙 _) g))
      (hg _ hY (isQuasiCompactSpace_yoneda B S hS Y inferInstance) (𝟙 _))
  obtain ⟨W, w, hWaff, hwS, hwE⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS V hV).mp hVqc
  have hw := locallySurjective_of_presheaf_surjective_etale B S hS w hwS
    (presheafEtale_of_isEtale B S hS w hwE)
    (isAlgebraicSpace_yoneda B S hS W).isSheaf hV.isSheaf
  obtain ⟨g₀, hg₀⟩ := yoneda.map_surjective (w ≫ g)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj W) := hWaff
  have : AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map g₀) := inferInstance
  have s' : IsPullback (yoneda.map (pullback.fst g₀ f)) (yoneda.map (pullback.snd g₀ f))
      (w ≫ g) (yoneda.map f) := hg₀ ▸ (IsPullback.of_hasPullback g₀ f).map yoneda
  have hKI : schemeTheoreticImageSubfunctor B S hS (yoneda.map g₀) =
      schemeTheoreticImageSubfunctor B S hS g := by
    rw [hg₀]
    exact schemeTheoreticImageSubfunctor_precomp_locallySurjective B S hS hY w g hw
  have hLJ : schemeTheoreticImageSubfunctor B S hS (yoneda.map (pullback.snd g₀ f)) =
      schemeTheoreticImageSubfunctor B S hS b := by
    have heq : sq.lift (yoneda.map (pullback.fst g₀ f) ≫ w)
        (yoneda.map (pullback.snd g₀ f)) (by rw [Category.assoc, s'.w]) ≫ b =
        yoneda.map (pullback.snd g₀ f) := sq.lift_snd _ _ _
    rw [← heq]
    exact schemeTheoreticImageSubfunctor_precomp_locallySurjective B S hS hX _ b
      (locallySurjective_of_isPullback _ (s'.of_bot' sq) hw)
  rw [← hLJ, ← hKI]
  exact schemeTheoreticImageSubfunctor_pullback_snd_yoneda_of_flat B S hS f g₀

/-- For étale charts `a` of `X` and `b` of `Y` fitting in a commuting square over `f` whose
morphism of schemes is flat, with `b` affine, the inverse images along `a` of the
scheme-theoretic image of the base change of `g` and of the inverse image of the
scheme-theoretic image of `g` agree. -/
private lemma schemeTheoreticImageSubfunctor_preimage_of_chart_square
    {X Y V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hV : IsAlgebraicSpace B S hS V) (f : X ⟶ Y) (g : V ⟶ Y)
    (hg : IsQuasiCompact B S hS g)
    {T U : BigFppfOver B S hS} (a : yoneda.obj T ⟶ X) (b : yoneda.obj U ⟶ Y) (k : T ⟶ U)
    (ha : IsEtale B S hS a) (hb : IsEtale B S hS b)
    (hcomm : yoneda.map k ≫ b = a ≫ f)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map k)] :
    (schemeTheoreticImageSubfunctor B S hS (pullback.snd g f)).preimage a =
      ((schemeTheoreticImageSubfunctor B S hS g).preimage f).preimage a := by
  have hT := isAlgebraicSpace_yoneda B S hS T
  have hU := isAlgebraicSpace_yoneda B S hS U
  have hP := isAlgebraicSpace_pullback B S hS g f hV hX hY
  have hVU := isAlgebraicSpace_pullback B S hS g b hV hU hY
  have hp : IsQuasiCompact B S hS (pullback.snd g f) :=
    isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback g f) hg
  have hq : IsQuasiCompact B S hS (pullback.snd g b) :=
    isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback g b) hg
  have hIU := schemeTheoreticImageSubfunctor_of_isPullback_of_isEtale B S hS hV hU hY
    (IsPullback.of_hasPullback g b) hg hb
  have hJT := schemeTheoreticImageSubfunctor_of_isPullback_of_isEtale B S hS hP hT hX
    (IsPullback.of_hasPullback (pullback.snd g f) a) hp ha
  have hK := schemeTheoreticImageSubfunctor_of_isPullback_of_flat_isAffine B S hS hVU k
    (pullback.snd g b) hq (IsPullback.of_hasPullback (pullback.snd g b) (yoneda.map k))
  have hKJT : schemeTheoreticImageSubfunctor B S hS
        (pullback.snd (pullback.snd g b) (yoneda.map k)) =
      schemeTheoreticImageSubfunctor B S hS (pullback.snd (pullback.snd g f) a) := by
    refine schemeTheoreticImageSubfunctor_congr_range B S hS _ _ hT ?_
    rw [← range_preimage_eq_of_isPullback
        (IsPullback.of_hasPullback (pullback.snd g b) (yoneda.map k)),
      ← range_preimage_eq_of_isPullback
        (IsPullback.of_hasPullback (pullback.snd g f) a),
      ← range_preimage_eq_of_isPullback (IsPullback.of_hasPullback g b),
      ← range_preimage_eq_of_isPullback (IsPullback.of_hasPullback g f)]
    show (Subfunctor.range g).preimage (yoneda.map k ≫ b) =
      (Subfunctor.range g).preimage (a ≫ f)
    rw [hcomm]
  rw [← hJT, ← hKJT, hK, hIU]
  show (schemeTheoreticImageSubfunctor B S hS g).preimage (yoneda.map k ≫ b) =
    (schemeTheoreticImageSubfunctor B S hS g).preimage (a ≫ f)
  rw [hcomm]

/-- For morphisms of presheaves on the big fppf category over `S` carrying algebraicity
hypotheses: for a flat `f : X ⟶ Y` and a quasi-compact `g : V ⟶ Y`, the
scheme-theoretic image of `V ×_Y X ⟶ X` is the inverse image along `f` of the scheme-theoretic
image of `g`. -/
@[ega "IV 2.3.2" "more general"]
theorem schemeTheoreticImageSubfunctor_pullback_snd_of_isFlat_of_isQuasiCompact'
    {X Y V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : V ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hV : IsAlgebraicSpace B S hS V) (hf : IsFlat B S hS f)
    (hg : IsQuasiCompact B S hS g) :
    schemeTheoreticImageSubfunctor B S hS (pullback.snd g f) =
      (schemeTheoreticImageSubfunctor B S hS g).preimage f := by
  obtain ⟨T, U, a, b, k, ha, hb, has, hcomm, -⟩ :=
    (isFlat_tfae B S hS hX hY f).out 1 8 |>.mp hf
  have hT := isAlgebraicSpace_yoneda B S hS T
  have hclosed := isClosedSubspace_preimage B S hS f
    (schemeTheoreticImageSubfunctor B S hS g) hY hX
    (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS g hY)
  have hJclosed :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS (pullback.snd g f) hX
  have haLocal := locallySurjective_of_presheaf_surjective_etale B S hS a
    ((presheafSurjective_iff_isSurjective_yoneda B S hS X hX T a).2 has)
    (presheafEtale_of_isEtale B S hS a ha) hT.isSheaf hX.isSheaf
  have he : (schemeTheoreticImageSubfunctor B S hS (pullback.snd g f)).preimage a =
      ((schemeTheoreticImageSubfunctor B S hS g).preimage f).preimage a := by
    refine closedSubspace_eq_of_affineOpen_cover B S hS T _ _
      (isClosedSubspace_preimage B S hS a _ hX hT hJclosed)
      (isClosedSubspace_preimage B S hS a _ hX hT hclosed)
      (ι := {p : ((BigFppfOver.toScheme B S hS).obj T).affineOpens ×
          ((BigFppfOver.toScheme B S hS).obj U).affineOpens //
          p.1.1 ≤ (BigFppfOver.toScheme B S hS).map k ⁻¹ᵁ p.2.1})
      (fun d => d.1.1) ?_ ?_
    · refine top_le_iff.mp fun x _ => ?_
      obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset
        (show (BigFppfOver.toScheme B S hS).map k x ∈
          (⊤ : ((BigFppfOver.toScheme B S hS).obj U).Opens) from trivial)
      obtain ⟨L, hL, hxL, hLW⟩ := exists_isAffineOpen_mem_and_subset
        (show x ∈ (BigFppfOver.toScheme B S hS).map k ⁻¹ᵁ W from hxW)
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨⟨L, hL⟩, ⟨W, hW⟩⟩, hLW⟩, hxL⟩
    · intro d
      have hi : (BigFppfOver.toScheme B S hS).map (siteOpenObjectι B S hS T d.1.1.1) =
          d.1.1.1.ι := siteOpenObjectι_map B S hS T d.1.1.1
      have hj : (BigFppfOver.toScheme B S hS).map (siteOpenObjectι B S hS U d.1.2.1) =
          d.1.2.1.ι := siteOpenObjectι_map B S hS U d.1.2.1
      have hjOI : AlgebraicGeometry.IsOpenImmersion
          ((BigFppfOver.toScheme B S hS).map (siteOpenObjectι B S hS U d.1.2.1)) := by
        rw [hj]; infer_instance
      have hrange : Set.range ((BigFppfOver.toScheme B S hS).map
            (siteOpenObjectι B S hS T d.1.1.1 ≫ k)).base ⊆
          Set.range ((BigFppfOver.toScheme B S hS).map
            (siteOpenObjectι B S hS U d.1.2.1)).base := by
        rw [hj, Scheme.Opens.range_ι]
        rintro _ ⟨z, rfl⟩
        show ((BigFppfOver.toScheme B S hS).map
          (siteOpenObjectι B S hS T d.1.1.1 ≫ k)).base z ∈ d.1.2.1
        rw [(BigFppfOver.toScheme B S hS).map_comp]
        exact d.2 (by rw [hi] at *; exact z.property)
      obtain ⟨l, hl⟩ := exists_hom_of_scheme_hom_comp B S hS
        (siteOpenObjectι B S hS U d.1.2.1) (siteOpenObjectι B S hS T d.1.1.1 ≫ k)
        (AlgebraicGeometry.IsOpenImmersion.lift _ _ hrange)
        (AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ hrange)
      have hai := presheafEtale_siteOpenObjectι_comp B S hS d.1.1.1 a ha
      have hbj := presheafEtale_siteOpenObjectι_comp B S hS d.1.2.1 b hb
      have hc : yoneda.map l ≫ (yoneda.map (siteOpenObjectι B S hS U d.1.2.1) ≫ b) =
          (yoneda.map (siteOpenObjectι B S hS T d.1.1.1) ≫ a) ≫ f := by
        rw [← Category.assoc, ← yoneda.map_comp, hl, yoneda.map_comp, Category.assoc,
          Category.assoc, ← hcomm]
      have : AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map l) :=
        hf _ _ _ _ l hai hbj hc
      have : IsAffine ((BigFppfOver.toScheme B S hS).obj
        (siteOpenObject B S hS U d.1.2.1)) := d.1.2.2
      exact schemeTheoreticImageSubfunctor_preimage_of_chart_square B S hS hX hY hV f g hg
        (yoneda.map (siteOpenObjectι B S hS T d.1.1.1) ≫ a)
        (yoneda.map (siteOpenObjectι B S hS U d.1.2.1) ≫ b) l
        (isEtale_of_presheafEtale B S hS _ hai) (isEtale_of_presheafEtale B S hS _ hbj) hc
  exact le_antisymm
    (subfunctor_le_of_preimage_le_of_locallySurjective (BigFppfOver.topology B S hS) a
      _ _ hX.isSheaf hclosed.1.isSheaf haLocal he.le)
    (subfunctor_le_of_preimage_le_of_locallySurjective (BigFppfOver.topology B S hS) a
      _ _ hX.isSheaf hJclosed.1.isSheaf haLocal he.ge)

/-- The scheme-theoretic image of a quasi-compact morphism `g : V ⟶ Y` of
algebraic spaces over `S` commutes with flat base change: for a flat `f : X ⟶ Y`, the
scheme-theoretic image of `V ×_Y X ⟶ X` is the inverse image along `f` of the scheme-theoretic
image of `g`. -/
@[stacks 089E, ega "IV 2.3.2"]
theorem schemeTheoreticImageSubfunctor_pullback_snd_of_isFlat_of_isQuasiCompact
    {X Y V : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : V ⟶ Y)
    (hf : IsFlat B S hS f.hom) (hg : IsQuasiCompact B S hS g.hom) :
    schemeTheoreticImageSubfunctor B S hS (pullback.snd g.hom f.hom) =
      (schemeTheoreticImageSubfunctor B S hS g.hom).preimage f.hom :=
  schemeTheoreticImageSubfunctor_pullback_snd_of_isFlat_of_isQuasiCompact' B S hS f.hom g.hom
    X.2 Y.2 V.2 hf hg

end AlgebraicGeometry.Space

end
