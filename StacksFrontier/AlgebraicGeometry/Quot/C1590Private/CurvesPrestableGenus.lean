module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyIsomQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSemistableGenus
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesStable
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFactorizationLocus

/-!
# The prestable curves of genus `g` (towards Stacks 0E6V)

Stacks 0E6V decomposes the open substack `Curves^{prestable}` of the stack of curves into open and
closed substacks `Curves^{prestable}_g`, `g ≥ 0`: a family of curves `f : X → S` lies in the
genus-`g` piece when it is prestable and `R¹f_*𝒪_X` is a locally free `𝒪_S`-module of rank `g`,
and a proper curve over a field lies in it when it is prestable of genus `g`.

The genus-`g` piece is cut out here by the genus of the *fibres*
(`AlgebraicGeometry.CurveFamily.HasFibresOfGenus`), so it is a strictly full subcategory stable
under base change with no cohomological input. Every family of curves has its fibres presented by
schemes (`AlgebraicGeometry.C1590Private.exists_isPullback_yoneda_fieldValuedPoint`), so the
genus loci of any family pull back along every morphism of families
(`AlgebraicGeometry.C1590Private.genusLocus_eq_preimage`) and partition its base.

Two inputs about `R¹f_*𝒪_X` are not available and enter as named hypotheses:

* `AlgebraicGeometry.C1590Private.PrestableGenusLociOpen`: on a prestable family the genus loci
  are open in the base. This is the local constancy of `s ↦ dim H¹(X_s, 𝒪_{X_s})`.
* `AlgebraicGeometry.C1590Private.PrestableHasGenusIff`: a prestable family has `R¹f_*𝒪_X`
  locally free of rank `g` exactly when all its fibres have genus `g`.

Both follow from Stacks 0E1J, parts (2) and (3), for prestable families: `R¹f_*𝒪_X` is finite
locally free and its formation commutes with arbitrary base change. The rank at a point is then the
dimension of `H¹` of the fibre. Given these, `Curves^{prestable}_g` has condition (o) of Section
0E0E relative to `Curves^{prestable}` (Stacks 0E6U, here the hypothesis `hpre`), and its families
are the prestable families with `R¹f_*𝒪_X` locally free of rank `g`.

## Main definitions

* `AlgebraicGeometry.C1590Private.IsPrestableCurveFamilyOfFibreGenus`: prestable with all
  fibres of genus `g`.
* `AlgebraicGeometry.C1590Private.curvesPrestableOfGenus`: the category fibred in groupoids
  `Curves^{prestable}_g`.
* `AlgebraicGeometry.C1590Private.PrestableGenusLociOpen` and
  `AlgebraicGeometry.C1590Private.PrestableHasGenusIff`: the two inputs about `R¹f_*𝒪_X`.

## Main results

* `AlgebraicGeometry.C1590Private.genusLocus_eq_preimage` and
  `AlgebraicGeometry.C1590Private.hasFibresOfGenus_iff_range_subset`: the genus loci of any family
  of curves commute with base change.
* `AlgebraicGeometry.C1590Private.disjoint_genusLocus_and_iUnion_genusLocus`: the genus loci of
  any family of curves partition its base.
* `AlgebraicGeometry.C1590Private.isOpen_inter_genusLocus`: over an open of the base on which the
  restricted family is prestable, the genus loci are open.
* `AlgebraicGeometry.C1590Private.isOpenCurvesLocus_and_hasFibresOfGenus` and
  `AlgebraicGeometry.C1590Private.isOpenCurvesLocus_isPrestableCurveFamilyOfFibreGenus`:
  condition (o) for the genus-`g` part of an open substack of prestable curves, and for
  `Curves^{prestable}_g`.
* `AlgebraicGeometry.C1590Private.prestable_genus_decomposition`: over a prestable family the
  genus loci are open and closed, pairwise disjoint and cover the base, and they describe the
  families mapping to it which lie in `Curves^{prestable}_g`.
* `AlgebraicGeometry.C1590Private.isPrestableCurveFamilyOfFibreGenus_iff_hasGenus` and
  `AlgebraicGeometry.C1590Private.hasGenus_of_hom`: part (1)(b) of Stacks 0E6V, and the genus of a
  prestable family is inherited along every morphism of families.

## Implementation notes

No declaration here carries a `stacks` attribute. The hypotheses `hpre` (Stacks 0E6U, the open
substack `Curves^{prestable}`), `hopen` and `hR` are arguments.

## References

* [Stacks Project, Tag 0E6V](https://stacks.math.columbia.edu/tag/0E6V)
* [Stacks Project, Tag 0E6U](https://stacks.math.columbia.edu/tag/0E6U)
* [Stacks Project, Tag 0E6K](https://stacks.math.columbia.edu/tag/0E6K)
* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.C1590Private

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-! ### The genus loci of an arbitrary family of curves -/

/-- The fibre of a family of curves at a field-valued point of its base is presented by a scheme:
the form of `AlgebraicGeometry.CurveFamily.exists_isPullback_fieldValuedPoint` used by the genus
loci. -/
theorem exists_isPullback_yoneda_fieldValuedPoint (X : CurveFamily B hZ)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj) :
    ∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject) (q : yoneda.obj V ⟶ X.total.obj),
      IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm p.value) := by
  obtain ⟨V, v, q, h⟩ := CurveFamily.exists_isPullback_fieldValuedPoint B hZ X p
  exact ⟨V, v, q.hom, AlgebraicSpaces.isPullback_hom B integerBase hZ h⟩

variable {B hZ}

/-- **The genus loci of any family of curves commute with base change.** -/
theorem genusLocus_eq_preimage {X Y : CurveFamily B hZ} (φ : X ⟶ Y) (g : ℕ) :
    X.genusLocus g =
      (BigFppfOver.toScheme B integerBase hZ).map φ.baseMap ⁻¹' Y.genusLocus g :=
  CurveFamily.genusLocus_eq_preimage φ (exists_isPullback_yoneda_fieldValuedPoint B hZ Y) g

/-- All fibres of a family of curves have genus `g` exactly when its genus-`g` locus is the whole
base. -/
theorem hasFibresOfGenus_iff_genusLocus_eq_univ (X : CurveFamily B hZ) (g : ℕ) :
    X.HasFibresOfGenus g ↔ X.genusLocus g = Set.univ :=
  CurveFamily.hasFibresOfGenus_iff_genusLocus_eq_univ
    (exists_isPullback_yoneda_fieldValuedPoint B hZ X) g

/-- A family of curves mapping to `Y` has all fibres of genus `g` exactly when its morphism of
bases lands in the genus-`g` locus of `Y`. -/
theorem hasFibresOfGenus_iff_range_subset {X Y : CurveFamily B hZ} (φ : X ⟶ Y) (g : ℕ) :
    X.HasFibresOfGenus g ↔
      Set.range ((BigFppfOver.toScheme B integerBase hZ).map φ.baseMap) ⊆ Y.genusLocus g := by
  rw [hasFibresOfGenus_iff_genusLocus_eq_univ, genusLocus_eq_preimage φ, Set.range_subset_iff,
    Set.eq_univ_iff_forall]
  rfl

/-- Every point of the base of a family of curves lies in the genus locus of the genus of the
fibre there. -/
theorem exists_mem_genusLocus (X : CurveFamily B hZ)
    (x : (BigFppfOver.toScheme B integerBase hZ).obj X.base) : ∃ g, x ∈ X.genusLocus g := by
  obtain ⟨V, v, q, hV⟩ := exists_isPullback_yoneda_fieldValuedPoint B hZ X (X.residueFieldPoint x)
  exact ⟨_, V, v, q, hV, rfl⟩

/-- **The genus loci of a family of curves partition its base.** -/
theorem disjoint_genusLocus_and_iUnion_genusLocus (X : CurveFamily B hZ) :
    Pairwise (fun g g' => Disjoint (X.genusLocus g) (X.genusLocus g')) ∧
      ⋃ g, X.genusLocus g = Set.univ :=
  ⟨fun _ _ h => X.disjoint_genusLocus h,
    Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 (exists_mem_genusLocus X x)⟩

/-- If all genus loci of a family of curves are open, then each of them is also closed: its
complement is the union of the other genus loci. -/
theorem isClosed_genusLocus_of_forall_isOpen (X : CurveFamily B hZ)
    (h : ∀ g, IsOpen (X.genusLocus g)) (g : ℕ) : IsClosed (X.genusLocus g) := by
  have hcompl : (X.genusLocus g)ᶜ = ⋃ g' ∈ {g' | g' ≠ g}, X.genusLocus g' := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    constructor
    · intro hx
      obtain ⟨g', hg'⟩ := exists_mem_genusLocus X x
      exact ⟨g', fun h => hx (h ▸ hg'), hg'⟩
    · rintro ⟨g', hne, hx'⟩ hx
      exact (X.disjoint_genusLocus hne).ne_of_mem hx' hx rfl
  exact isOpen_compl_iff.mp (hcompl ▸ isOpen_biUnion fun g' _ => h g')

/-! ### The inputs about `R¹f_*𝒪_X` -/

variable (B hZ)

/-- **Input: the genus loci of a prestable family are open.** On a prestable family of curves
`f : X → S` the function `s ↦ dim H¹(X_s, 𝒪_{X_s})` is locally constant, so each genus locus is
open in `S`. This follows from Stacks 0E1J, parts (2) and (3): `R¹f_*𝒪_X` is finite locally free,
its formation commutes with base change, and its rank at `s` is `dim H¹(X_s, 𝒪_{X_s})`. -/
def PrestableGenusLociOpen : Prop :=
  ∀ X : CurveFamily B hZ, IsPrestableCurveFamily B hZ X → ∀ g : ℕ, IsOpen (X.genusLocus g)

/-- **Input: the genus of a prestable family is the rank of `R¹f_*𝒪_X`.** A prestable family of
curves `f : X → S` has `R¹f_*𝒪_X` locally free of rank `g` exactly when all its fibres have genus
`g`. This follows from Stacks 0E1J, parts (2) and (3), as for
`AlgebraicGeometry.C1590Private.PrestableGenusLociOpen`. -/
def PrestableHasGenusIff : Prop :=
  ∀ X : CurveFamily B hZ, IsPrestableCurveFamily B hZ X → ∀ g : ℕ,
    CurveFamily.HasGenus B hZ X g ↔ X.HasFibresOfGenus g

/-! ### The genus-`g` piece -/

/-- A family of curves is *prestable of genus `g`* when it is prestable (Stacks 0E6T) and all its
fibres have genus `g`. -/
abbrev IsPrestableCurveFamilyOfFibreGenus (g : ℕ) (X : CurveFamily B hZ) : Prop :=
  IsPrestableCurveFamily B hZ X ∧ X.HasFibresOfGenus g

/-- A family of curves mapping to a prestable family of genus `g` is prestable of genus `g`. -/
theorem isPrestableCurveFamilyOfFibreGenus_of_hom (g : ℕ) {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    (hY : IsPrestableCurveFamilyOfFibreGenus B hZ g Y) :
    IsPrestableCurveFamilyOfFibreGenus B hZ g X :=
  ⟨CurveFamily.isPrestableCurveFamily_of_hom φ hY.1, hY.2.of_hom φ⟩

/-- Being prestable of genus `g` is invariant under isomorphism of families of curves. -/
theorem isPrestableCurveFamilyOfFibreGenus_isClosedUnderIsomorphisms (g : ℕ) :
    (show ObjectProperty (CurveFamily B hZ) from
      IsPrestableCurveFamilyOfFibreGenus B hZ g).IsClosedUnderIsomorphisms :=
  ⟨fun e hX => isPrestableCurveFamilyOfFibreGenus_of_hom B hZ g e.inv hX⟩

/-- The category fibred in groupoids `Curves^{prestable}_g` of prestable families of curves of
genus `g`, a strictly full subcategory of the stack of curves. -/
noncomputable abbrev curvesPrestableOfGenus (g : ℕ) :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B integerBase hZ) :=
  curvesSubstack B hZ (IsPrestableCurveFamilyOfFibreGenus B hZ g)
    (isPrestableCurveFamilyOfFibreGenus_of_hom B hZ g)

variable {B hZ}

/-- A prestable family of curves lies in the genus-`g` piece exactly when `R¹f_*𝒪_X` is locally
free of rank `g`: condition (1)(b) of Stacks 0E6V, given the input `hR`. -/
theorem isPrestableCurveFamilyOfFibreGenus_iff_hasGenus (hR : PrestableHasGenusIff B hZ)
    (g : ℕ) (X : CurveFamily B hZ) :
    IsPrestableCurveFamilyOfFibreGenus B hZ g X ↔
      IsPrestableCurveFamily B hZ X ∧ CurveFamily.HasGenus B hZ X g :=
  ⟨fun h => ⟨h.1, (hR X h.1 g).2 h.2⟩, fun h => ⟨h.1, (hR X h.1 g).1 h.2⟩⟩

/-- **The genus of a prestable family is inherited along every morphism of families**, given the
input `hR`: the genus of the fibres pulls back. -/
theorem hasGenus_of_hom (hR : PrestableHasGenusIff B hZ) {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    (hY : IsPrestableCurveFamily B hZ Y) {g : ℕ} (h : CurveFamily.HasGenus B hZ Y g) :
    CurveFamily.HasGenus B hZ X g :=
  ((isPrestableCurveFamilyOfFibreGenus_iff_hasGenus hR g X).1
    (isPrestableCurveFamilyOfFibreGenus_of_hom B hZ g φ
      ((isPrestableCurveFamilyOfFibreGenus_iff_hasGenus hR g Y).2 ⟨hY, h⟩))).2

/-! ### Openness -/

/-- A morphism of the site lands in a set of points of the scheme of its target exactly when its
morphism of points lands in the corresponding set of points of the represented algebraic space. -/
theorem range_pointsMap_subset_preimage_iff {U V : BigFppfOver B integerBase hZ} (f : U ⟶ V)
    (Ω : Set ((BigFppfOver.toScheme B integerBase hZ).obj V)) :
    Set.range (Space.pointsMap B integerBase hZ (yoneda.obj U) (yoneda.map f)) ⊆
        Space.schemePointsHomeomorph B integerBase hZ V ⁻¹' Ω ↔
      Set.range ((BigFppfOver.toScheme B integerBase hZ).map f) ⊆ Ω := by
  simp only [Set.range_subset_iff, Set.mem_preimage, Space.schemePointsHomeomorph_apply,
    Space.pointsToScheme_pointsMap_yoneda]
  refine ⟨fun h x => ?_, fun h w => h _⟩
  obtain ⟨w, rfl⟩ := (Space.schemePointsHomeomorph B integerBase hZ U).surjective x
  exact h w

/-- The points of the represented algebraic space through which a morphism of the site factors
are those over the image of the morphism of schemes. -/
theorem range_pointsMap_yoneda {U V : BigFppfOver B integerBase hZ} (f : U ⟶ V) :
    Set.range (Space.pointsMap B integerBase hZ (yoneda.obj U) (yoneda.map f)) =
      Space.schemePointsHomeomorph B integerBase hZ V ⁻¹'
        Set.range ((BigFppfOver.toScheme B integerBase hZ).map f) := by
  ext w
  simp only [Set.mem_range, Set.mem_preimage, Space.schemePointsHomeomorph_apply]
  constructor
  · rintro ⟨w', rfl⟩
    exact ⟨_, (Space.pointsToScheme_pointsMap_yoneda B integerBase hZ f w').symm⟩
  · rintro ⟨x, hx⟩
    obtain ⟨w', rfl⟩ := (Space.schemePointsHomeomorph B integerBase hZ U).surjective x
    refine ⟨w', (Space.schemePointsHomeomorph B integerBase hZ V).injective ?_⟩
    rw [Space.schemePointsHomeomorph_apply, Space.schemePointsHomeomorph_apply,
      Space.pointsToScheme_pointsMap_yoneda, ← hx]
    rfl

/-- **The genus loci are open over a prestable open.** Let `j : V ⟶ S` be an open immersion into
the base of a family of curves `G` such that the family restricted to `V` is prestable. Then the
part of each genus locus of `G` lying over `V` is open, given the input `hopen`. -/
theorem isOpen_inter_genusLocus (hopen : PrestableGenusLociOpen B hZ) (G : CurveFamily B hZ)
    {V : BigFppfOver B integerBase hZ} (j : V ⟶ G.base)
    (hj : IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map j))
    (hpre : ∀ (F : CurveFamily B hZ) (a : F ⟶ G),
      Set.range ((BigFppfOver.toScheme B integerBase hZ).map a.baseMap) ⊆
        Set.range ((BigFppfOver.toScheme B integerBase hZ).map j) → IsPrestableCurveFamily B hZ F)
    (g : ℕ) :
    IsOpen (Set.range ((BigFppfOver.toScheme B integerBase hZ).map j) ∩ G.genusLocus g) := by
  set T := BigFppfOver.toScheme B integerBase hZ
  obtain ⟨G₀, φ, h, hφ⟩ := CurveFamily.exists_hom_baseMap_eq G j
  have hφT : T.map φ.baseMap = T.map (eqToHom h) ≫ T.map j := by rw [hφ, T.map_comp]
  have hrange : Set.range (T.map φ.baseMap) = Set.range (T.map j) := by
    rw [hφT, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      ((ConcreteCategory.bijective_of_isIso (T.map (eqToHom h)).base)).2.range_eq, Set.image_univ]
  have hG₀ : IsPrestableCurveFamily B hZ G₀ := hpre G₀ φ hrange.le
  have himage : T.map φ.baseMap '' G₀.genusLocus g =
      Set.range (T.map j) ∩ G.genusLocus g := by
    rw [genusLocus_eq_preimage φ, Set.image_preimage_eq_range_inter, hrange]
  have : IsOpenImmersion (T.map φ.baseMap) := by
    rw [hφT]
    infer_instance
  rw [← himage]
  exact (T.map φ.baseMap).isOpenEmbedding.isOpenMap _ (hopen G₀ hG₀ g)

/-- **Condition (o) of Stacks 0E0E for the genus-`g` part of an open substack of prestable
curves.** Let `P` be a property of families of curves with condition (o) (an open substack
`Curves^P` of `Curves`) all of whose families are prestable. Given the openness of the genus loci
of prestable families (the input `hopen`), the families with `P` all of whose fibres have genus
`g` again have condition (o): over a family `G`, the locus is the part of the genus-`g` locus of
`G` lying over the `P`-locus of `G`. -/
theorem isOpenCurvesLocus_and_hasFibresOfGenus {P : ObjectProperty (CurveFamily B hZ)}
    (hP : IsOpenCurvesLocus B hZ P) (hPpre : ∀ X, P X → IsPrestableCurveFamily B hZ X)
    (hopen : PrestableGenusLociOpen B hZ) (g : ℕ) :
    IsOpenCurvesLocus B hZ (fun X => P X ∧ X.HasFibresOfGenus g) := by
  refine IsOpenCurvesLocus.of_points fun G => ?_
  set T := BigFppfOver.toScheme B integerBase hZ
  obtain ⟨W, hW, hchar⟩ := hP G
  obtain ⟨V, j, hj, e, he⟩ : ∃ (V : BigFppfOver B integerBase hZ) (j : V ⟶ G.base),
      IsOpenImmersion (T.map j) ∧ ∃ e : yoneda.obj V ≅ W.toFunctor, e.hom ≫ W.ι = yoneda.map j := by
    have h := hW.2.rep.isPullback (𝟙 (yoneda.obj G.base))
    have := h.isIso_fst_of_isIso (inst := IsIso.id _)
    exact ⟨_, hW.2.rep.snd (𝟙 (yoneda.obj G.base)), hW.2.property_snd _,
      asIso (hW.2.rep.fst (𝟙 (yoneda.obj G.base))), h.w.trans (Category.comp_id _)⟩
  have hι : Set.range (Space.pointsMap B integerBase hZ W.toFunctor W.ι) =
      Set.range (Space.pointsMap B integerBase hZ (yoneda.obj V) (yoneda.map j)) := by
    rw [← he]
    exact (Space.range_pointsMap_comp_isIso B integerBase hZ e.hom W.ι).symm
  have hpreF : ∀ (F : CurveFamily B hZ) (a : F ⟶ G),
      P F ↔ Set.range (T.map a.baseMap) ⊆ Set.range (T.map j) := by
    intro F a
    refine (hchar F a).trans ((Space.factorsThrough_openSubspace_iff_points B integerBase hZ
      (schemeSpace G.base).property (schemeSpace F.base).property W hW _).trans ?_)
    rw [hι, range_pointsMap_yoneda j]
    exact range_pointsMap_subset_preimage_iff a.baseMap _
  refine ⟨Space.schemePointsHomeomorph B integerBase hZ G.base ⁻¹'
      (Set.range (T.map j) ∩ G.genusLocus g),
    (isOpen_inter_genusLocus hopen G j hj (fun F a h => hPpre F ((hpreF F a).2 h)) g).preimage
      (Space.schemePointsHomeomorph B integerBase hZ G.base).continuous, fun F a => ?_⟩
  refine Iff.trans ?_ (range_pointsMap_subset_preimage_iff a.baseMap _).symm
  rw [Set.subset_inter_iff, ← hpreF F a, ← hasFibresOfGenus_iff_range_subset a]

/-- **Condition (o) of Stacks 0E0E for `Curves^{prestable}_g`**, from the open substack
`Curves^{prestable}` (Stacks 0E6U, the hypothesis `hpre`) and the openness of the genus loci of
prestable families (the input `hopen`). -/
theorem isOpenCurvesLocus_isPrestableCurveFamilyOfFibreGenus
    (hpre : IsOpenCurvesLocus B hZ (IsPrestableCurveFamily B hZ))
    (hopen : PrestableGenusLociOpen B hZ) (g : ℕ) :
    IsOpenCurvesLocus B hZ (IsPrestableCurveFamilyOfFibreGenus B hZ g) :=
  isOpenCurvesLocus_and_hasFibresOfGenus hpre (fun _ h => h) hopen g

/-- **The decomposition of `Curves^{prestable}` by genus over a prestable family**, given the
input `hopen`. For a prestable family of curves `G` over `S`, the genus loci `Ω_g` of `G` are open
and closed in `S`, pairwise disjoint and cover `S`, and a family of curves mapping to `G` is
prestable of genus `g` exactly when its morphism of bases lands in `Ω_g`: the base change of
`Curves^{prestable}_g ⊂ Curves^{prestable}` along `S → Curves^{prestable}` is the open and closed
subscheme `Ω_g`, and these partition `S`. -/
theorem prestable_genus_decomposition (hopen : PrestableGenusLociOpen B hZ)
    (G : CurveFamily B hZ) (hG : IsPrestableCurveFamily B hZ G) :
    ∃ Ω : ℕ → Set ((BigFppfOver.toScheme B integerBase hZ).obj G.base),
      (∀ g, IsOpen (Ω g) ∧ IsClosed (Ω g)) ∧ Pairwise (fun g g' => Disjoint (Ω g) (Ω g')) ∧
        ⋃ g, Ω g = Set.univ ∧
        ∀ (g : ℕ) (F : CurveFamily B hZ) (a : F ⟶ G),
          IsPrestableCurveFamilyOfFibreGenus B hZ g F ↔
            Set.range ((BigFppfOver.toScheme B integerBase hZ).map a.baseMap) ⊆ Ω g :=
  ⟨G.genusLocus, fun g => ⟨hopen G hG g,
      isClosed_genusLocus_of_forall_isOpen G (hopen G hG) g⟩,
    (disjoint_genusLocus_and_iUnion_genusLocus G).1,
    (disjoint_genusLocus_and_iUnion_genusLocus G).2, fun g _ a =>
      (and_iff_right (CurveFamily.isPrestableCurveFamily_of_hom a hG)).trans
        (hasFibresOfGenus_iff_range_subset a g)⟩

end AlgebraicGeometry.C1590Private

end
