module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFibreGenusRank
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOfSchemeFibreGenus
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesReducedConnectedGeometricFibres
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesStable
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesOfGenusOverField
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectPropertyClosedLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectPropertyOpenImmersion
public import StacksFrontier.CategoryTheory.Sites.Stack.FullSubcategorySliceLocus

/-!
# The decomposition of `Curves^{grc,1}` by genus (Stacks 0E1K)

Let `Curves^{grc,1}` be the stack of families of curves `f : X → S` whose geometric fibres are
reduced, connected and of dimension `1` (`AlgebraicGeometry.curvesGrcDimOne`). Stacks 0E1K
decomposes it into the open and closed substacks `Curves^{grc,1}_g`, `g ≥ 0`, of the families
with `R¹f_*𝒪_X` locally free of rank `g`.

## Main definitions

* `AlgebraicGeometry.IsGrcDimOneFibreGenus`: an object of `Curves^{grc,1}` all of whose fibres
  over fields have genus `g`.
* `AlgebraicGeometry.curvesGrcDimOneOfGenus`: the full subcategory `Curves^{grc,1}_g` of
  `Curves^{grc,1}` it cuts out, as a category fibred in groupoids over the big fppf site of
  `Spec(ℤ)`, and `AlgebraicGeometry.curvesGrcDimOneOfGenusInclusion` its inclusion into
  `Curves^{grc,1}`.

## Main results

* `AlgebraicGeometry.curvesGrcDimOneOfGenusInclusion_isOpenImmersion_and_isClosedImmersion`:
  `Curves^{grc,1}_g ⊂ Curves^{grc,1}` is an open and closed substack.
* `AlgebraicGeometry.curvesGrcDimOne_fibreGenusLocus`: over the base of every object of
  `Curves^{grc,1}` the loci of the `Curves^{grc,1}_g` are open and closed, pairwise disjoint,
  and cover the base: `Curves^{grc,1} = ∐_g Curves^{grc,1}_g`.
* `AlgebraicGeometry.factors_curvesGrcDimOneOfGenus_iff`: part (1) of Stacks 0E1K.
* `AlgebraicGeometry.factors_curvesGrcDimOneOfGenus_over_field_iff`: part (2) of Stacks 0E1K.
* `AlgebraicGeometry.curvesGrcDimOne_genus_decomposition`: **Stacks 0E1K**.

## Implementation notes

This is the second proof of the source: the decomposition is the one of Section 0E0E, cut out
on the base of every family in `Curves^{grc,1}` by the rank of the finite locally free module
`R¹f_*𝒪_X` (Stacks 0E1J, which applies because a family with reduced connected geometric fibres
has `k = H⁰(X_k, 𝒪_{X_k})` on its fibres over fields, Stacks 0E0S). Its formation commutes with
base change, and the rank at a point is the genus of the fibre there
(`AlgebraicGeometry.CurveFamily.fibreGenusLocus_eq_rankLocus`). `Curves^{grc,1}_g` is defined by
"every fibre over a field has genus `g`"
(`AlgebraicGeometry.CurveFamily.HasFieldPointFibreGenus`), which is visibly inherited along
morphisms of families, and part (1) identifies it with "`R¹f_*𝒪_X` is
locally free of rank `g`".

An open (resp. closed) substack of `Curves^{grc,1}` is, as in Stacks 04YM read for a category
fibred in groupoids, a strictly full subcategory whose inclusion is representable by algebraic
spaces and an open (resp. closed) immersion in the sense of Stacks 04XB. The open and closed
subscheme of the base of a scheme-valued point of `Curves^{grc,1}` along which it lies in
`Curves^{grc,1}_g` is the fibre genus locus of `g` of the family it classifies. The openness of
`Curves^{grc,1}` in `Curves` (Stacks 0E1I) is not used, nor stated here.

## References

* [Stacks Project, Tag 0E1K](https://stacks.math.columbia.edu/tag/0E1K)
* [Stacks Project, Tag 0E1I](https://stacks.math.columbia.edu/tag/0E1I)
* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
* [Stacks Project, Tag 0E6L](https://stacks.math.columbia.edu/tag/0E6L)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **The open subscheme of the base of a scheme-valued point cut out by an open set of
points.** Let `y` be a scheme-valued point of the stack of curves over `U` and let `Ω` be an open
set of points of the base of the family `y(U)` it classifies, such that `y(T)` has a property `Q`
exactly when the morphism from its base to that of `y(U)` sends every point into `Ω`. Then there
is an open subscheme `V` of `U` through which an object `T` of the big fppf site of `U` maps
exactly when `y(T)` has `Q`; when `Ω` is also closed, `V` is also a closed subscheme. -/
theorem exists_open_over_of_points {Q : ObjectProperty (CurveFamily B hZ)}
    (U : BigFppfOver B integerBase hZ) (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ)
    (hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom)
    (Ω : Set (Space.points B integerBase hZ (schemeSpace (y.obj (Over.mk (𝟙 U.left))).base).obj))
    (hΩ : IsOpen Ω)
    (hchar : ∀ (T : BigFppfOver B U.left.1 U.left.2) (t : T ⟶ Over.mk (𝟙 U.left)),
      Q (y.obj T) ↔ Set.range (Space.pointsMap B integerBase hZ (schemeSpace (y.obj T).base).obj
        (schemeSpaceMap (y.map t).baseMap).hom) ⊆ Ω) :
    ∃ V : BigFppfOver B U.left.1 U.left.2, IsOpenImmersion V.hom.hom ∧
      (IsClosed Ω → IsClosedImmersion V.hom.hom) ∧
      ∀ T : BigFppfOver B U.left.1 U.left.2, Nonempty (T ⟶ V) ↔ Q (y.obj T) := by
  let T₀ : BigFppfOver B U.left.1 U.left.2 := Over.mk (𝟙 U.left)
  let G := y.obj T₀
  let W := Space.openSubspaceOfPoints B integerBase hZ (schemeSpace G.base).obj Ω
  have hW : Space.IsOpenSubspace B integerBase hZ W :=
    Space.isOpenSubspace_openSubspaceOfPoints B integerBase hZ (schemeSpace G.base).property Ω hΩ
  have hWchar : ∀ (T : BigFppfOver B U.left.1 U.left.2) (t : T ⟶ T₀),
      Q (y.obj T) ↔ ∃ s : (schemeSpace (y.obj T).base).obj ⟶ W.toFunctor,
        s ≫ W.ι = (schemeSpaceMap (y.map t).baseMap).hom := by
    intro T t
    rw [Space.factorsThrough_openSubspace_iff_points B integerBase hZ
      (schemeSpace G.base).property (schemeSpace (y.obj T).base).property _ hW,
      Space.range_pointsMap_ι_openSubspaceOfPoints]
    exact hchar T t
  obtain ⟨V₀, j, hj, e, he⟩ : ∃ (V : BigFppfOver B integerBase hZ) (j : V ⟶ G.base),
      IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map j) ∧
      ∃ e : yoneda.obj V ≅ W.toFunctor, e.hom ≫ W.ι = yoneda.map j := by
    have key : ∀ (U' : BigFppfOver B integerBase hZ) (W' : Subfunctor (yoneda.obj U')),
        Space.IsOpenSubspace B integerBase hZ W' →
        ∃ (V : BigFppfOver B integerBase hZ) (j : V ⟶ U'),
          IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map j) ∧
          ∃ e : yoneda.obj V ≅ W'.toFunctor, e.hom ≫ W'.ι = yoneda.map j := by
      intro U' W' hW'
      let h := hW'.2.rep.isPullback (𝟙 (yoneda.obj U'))
      let eMap := hW'.2.rep.fst (𝟙 (yoneda.obj U'))
      have : IsIso eMap := h.isIso_fst_of_isIso
      exact ⟨_, hW'.2.rep.snd (𝟙 (yoneda.obj U')), hW'.2.property_snd (𝟙 (yoneda.obj U')),
        asIso eMap, by simpa [eMap] using h.w⟩
    exact key G.base W hW
  have hb : ∀ T : BigFppfOver B U.left.1 U.left.2,
      (y.obj T).base = (Over.map U.hom).obj T := fun T => congrArg (fun F => F.obj T) hy
  have h₂ : (Over.map U.hom).obj T₀ = U := by
    cases U
    congr 1
  let β : G.base ≅ U := eqToIso ((hb T₀).trans h₂)
  let V : BigFppfOver B U.left.1 U.left.2 := Over.mk (j ≫ β.hom).left
  have hVhom : V.hom.hom = (BigFppfOver.toScheme B integerBase hZ).map (j ≫ β.hom) := rfl
  refine ⟨V, ?_, fun hcl => ?_, fun T => Iff.symm ?_⟩
  · rw [hVhom, Functor.map_comp]
    infer_instance
  · -- the range of `V ⟶ U` is the image of `Ω` in the scheme `U`, a closed set
    rw [hVhom, Functor.map_comp]
    refine IsClosedImmersion.of_isPreimmersion _ ?_
    have hrange : Set.range ((BigFppfOver.toScheme B integerBase hZ).map j) =
        Space.schemePointsHomeomorph B integerBase hZ G.base '' Ω := by
      have hj' : ∀ w, Space.pointsMap B integerBase hZ (yoneda.obj V₀) (yoneda.map j) w =
          Space.pointsMap B integerBase hZ W.toFunctor W.ι
            (Space.pointsMap B integerBase hZ (yoneda.obj V₀) e.hom w) := by
        intro w
        induction w using Quot.ind
        rw [← he]
        rfl
      have hrj : Set.range (Space.pointsMap B integerBase hZ (yoneda.obj V₀) (yoneda.map j)) =
          Ω := by
        rw [← Space.range_pointsMap_ι_openSubspaceOfPoints B integerBase hZ
          (F := (schemeSpace G.base).obj) Ω]
        ext x
        constructor
        · rintro ⟨w, rfl⟩
          exact ⟨_, (hj' w).symm⟩
        · rintro ⟨w, rfl⟩
          obtain ⟨v, rfl⟩ := (Space.pointsHomeomorphOfIso B integerBase hZ e).surjective w
          exact ⟨v, hj' v⟩
      rw [← hrj, ← Set.range_comp]
      ext x
      constructor
      · rintro ⟨z, rfl⟩
        obtain ⟨w, rfl⟩ := (Space.schemePointsHomeomorph B integerBase hZ V₀).surjective z
        exact ⟨w, Space.pointsToScheme_pointsMap_yoneda B integerBase hZ j w⟩
      · rintro ⟨w, rfl⟩
        exact ⟨_, (Space.pointsToScheme_pointsMap_yoneda B integerBase hZ j w).symm⟩
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange]
    exact (Scheme.Hom.homeomorph ((BigFppfOver.toScheme B integerBase hZ).map β.hom)).isClosedMap _
      ((Space.schemePointsHomeomorph B integerBase hZ G.base).isClosedMap _ hcl)
  let t : T ⟶ T₀ := Over.homMk T.hom (by simp [T₀])
  let a : y.obj T ⟶ G := y.map t
  have hcomm : a.baseMap ≫ β.hom =
      eqToHom (hb T) ≫ (Over.homMk T.hom : (Over.map U.hom).obj T ⟶ U) := by
    have hm := Functor.congr_hom hy t
    have hcanon : (Over.map U.hom).map t ≫ eqToHom h₂ =
        (Over.homMk T.hom : (Over.map U.hom).obj T ⟶ U) := by
      cases U
      rfl
    change (curvesProjectionOver B hZ).map (y.map t) = _ at hm
    change (curvesProjectionOver B hZ).map (y.map t) ≫ eqToHom ((hb T₀).trans h₂) = _
    rw [hm, ← hcanon, Category.assoc, Category.assoc]
    exact congrArg (fun k => eqToHom (hb T) ≫ (Over.map U.hom).map t ≫ k) (eqToHom_trans _ _)
  rw [hWchar T t]
  change (∃ s : yoneda.obj (y.obj T).base ⟶ W.toFunctor, s ≫ W.ι = yoneda.map a.baseMap) ↔ _
  have hgen : ∀ {U' V' A : BigFppfOver B integerBase hZ} (W' : Subfunctor (yoneda.obj U'))
      (j' : V' ⟶ U') (e' : yoneda.obj V' ≅ W'.toFunctor) (_he' : e'.hom ≫ W'.ι = yoneda.map j')
      (a' : A ⟶ U'),
      (∃ s : yoneda.obj A ⟶ W'.toFunctor, s ≫ W'.ι = yoneda.map a') ↔
        ∃ k : A ⟶ V', k ≫ j' = a' := by
    intro U' V' A W' j' e' he' a'
    have he'' : e'.inv ≫ yoneda.map j' = W'.ι := by
      rw [← he', ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    constructor
    · rintro ⟨s, hs⟩
      refine ⟨yoneda.preimage (s ≫ e'.inv), yoneda.map_injective ?_⟩
      rw [Functor.map_comp, yoneda.map_preimage, Category.assoc, he'', hs]
    · rintro ⟨k, hk⟩
      exact ⟨yoneda.map k ≫ e'.hom, by rw [Category.assoc, he', ← Functor.map_comp, hk]⟩
  have hfac := hgen (U' := G.base) W j e he a.baseMap
  refine hfac.trans ?_
  have hc := congrArg (fun m => m.left) hcomm
  simp only [Over.comp_left] at hc
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨Over.homMk (eqToHom (congrArg Comma.left (hb T)).symm ≫ k.left) ?_⟩
    have hk' := congrArg (fun m => (m ≫ β.hom).left) hk
    simp only [Over.comp_left] at hk'
    change (eqToHom _ ≫ k.left) ≫ (j ≫ β.hom).left = T.hom
    rw [Over.comp_left, Category.assoc, ← Category.assoc k.left, hk', hc, Over.eqToHom_left]
    simp
  · rintro ⟨k⟩
    let l : (y.obj T).base ⟶ V₀ := Over.homMk
      (eqToHom (congrArg Comma.left (hb T)) ≫ k.left) (by
        apply ObjectProperty.hom_ext
        exact specULiftZIsTerminal.hom_ext _ _)
    refine ⟨l, (cancel_mono β.hom).mp (Over.OverMorphism.ext ?_)⟩
    simp only [Over.comp_left]
    rw [hc, Over.eqToHom_left]
    change (eqToHom _ ≫ k.left) ≫ j.left ≫ β.hom.left = _
    have hkw : k.left ≫ j.left ≫ β.hom.left = T.hom :=
      (Over.w k : k.left ≫ (j ≫ β.hom).left = T.hom)
    rw [Category.assoc, hkw]
    rfl

/-! ### The substack `Curves^{grc,1}_g` -/

variable (B hZ) in
/-- **The condition of `Curves^{grc,1}_g`**, on an object of `Curves^{grc,1}`: every fibre over a
field has genus `g` (`AlgebraicGeometry.CurveFamily.HasFieldPointFibreGenus`). By part (1) of
Stacks 0E1K (`AlgebraicGeometry.factors_curvesGrcDimOneOfGenus_iff`) this is `R¹f_*𝒪_X` being
locally free of rank `g`. -/
def IsGrcDimOneFibreGenus (g : ℕ) : ObjectProperty (IsGrcDimOneFamily B hZ).FullSubcategory :=
  fun X => CurveFamily.HasFieldPointFibreGenus B hZ X.obj g

/-- The condition of `Curves^{grc,1}_g` is inherited along morphisms of `Curves^{grc,1}`. -/
theorem isGrcDimOneFibreGenus_of_hom {g : ℕ} {X Y : (IsGrcDimOneFamily B hZ).FullSubcategory}
    (a : X ⟶ Y) (hY : IsGrcDimOneFibreGenus B hZ g Y) : IsGrcDimOneFibreGenus B hZ g X :=
  CurveFamily.hasFieldPointFibreGenus_of_hom a.hom hY

variable (B hZ) in
/-- **The stack `Curves^{grc,1}_g`** (Stacks 0E1K): the full subcategory of `Curves^{grc,1}` of
the families all of whose fibres over fields have genus `g`, as a category fibred in groupoids
over the big fppf site of `Spec(ℤ)`. -/
def curvesGrcDimOneOfGenus (g : ℕ) :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B integerBase hZ) :=
  CatFiberedInGroupoids.mk
    (Stack.objectPropertySubcategory B integerBase hZ (curvesGrcDimOne B hZ).val
      (IsGrcDimOneFibreGenus B hZ g))
    (Functor.isFiberedInGroupoids_restrict_of_hom (curvesGrcDimOne B hZ).val.p
      (curvesGrcDimOne B hZ).isFiberedInGroupoids _ isGrcDimOneFibreGenus_of_hom)

variable (B hZ) in
/-- The inclusion `Curves^{grc,1}_g ⟶ Curves^{grc,1}`, as a 1-morphism of categories fibred in
groupoids over the big fppf site of `Spec(ℤ)`. -/
def curvesGrcDimOneOfGenusInclusion (g : ℕ) :
    curvesGrcDimOneOfGenus B hZ g ⟶ curvesGrcDimOne B hZ :=
  Bicategory.InducedBicategory.mkHom
    (Stack.objectPropertyInclusion B integerBase hZ (curvesGrcDimOne B hZ).val
      (IsGrcDimOneFibreGenus B hZ g))

/-- A family in `Curves^{grc,1}` has all fibres of genus `g` exactly when the base of the family
maps into the fibre genus locus of `g` of any family in `Curves^{grc,1}` it maps to. -/
private theorem hasFieldPointFibreGenus_iff_range_pointsMap_subset {X F : CurveFamily B hZ}
    (hX : IsGrcDimOneFamily B hZ X) (hF : IsGrcDimOneFamily B hZ F) (a : F ⟶ X) (g : ℕ) :
    CurveFamily.HasFieldPointFibreGenus B hZ F g ↔
      Set.range (Space.pointsMap B integerBase hZ (schemeSpace F.base).obj
        (schemeSpaceMap a.baseMap).hom) ⊆ CurveFamily.fibreGenusLocus B hZ X g := by
  rw [F.hasFieldPointFibreGenus_iff_fibreGenusLocus_eq_univ
      (CurveFamily.bijective_algebraMap_fibre_of_isGrcDimOneFamily hF) g,
    ← X.preimage_fibreGenusLocus (CurveFamily.bijective_algebraMap_fibre_of_isGrcDimOneFamily hX)
      a (CurveFamily.bijective_algebraMap_fibre_of_isGrcDimOneFamily hF) g,
    Set.range_subset_iff, Set.eq_univ_iff_forall]
  rfl

/-- **The open and closed locus of `Curves^{grc,1}_g`.** Every scheme-valued point `y` of
`Curves^{grc,1}` over `U` cuts out an open and closed subscheme of `U` through which an object
`T` of the big fppf site of `U` maps exactly when `y(T)` lies in `Curves^{grc,1}_g`: the fibre
genus locus of `g` of the family `y(U)`, which is open and closed (the rank locus of the finite
locally free module `R¹f_*𝒪_X`) and compatible with base change. -/
theorem exists_clopen_over_isGrcDimOneFibreGenus (g : ℕ) (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ (curvesGrcDimOne B hZ).val.obj)
    (hy : y ⋙ (curvesGrcDimOne B hZ).val.p = Over.map U.hom) :
    ∃ V : BigFppfOver B U.left.1 U.left.2, IsOpenImmersion V.hom.hom ∧
      IsClosedImmersion V.hom.hom ∧
      ∀ T : BigFppfOver B U.left.1 U.left.2,
        Nonempty (T ⟶ V) ↔ IsGrcDimOneFibreGenus B hZ g (y.obj T) := by
  let y' := y ⋙ (IsGrcDimOneFamily B hZ).ι
  have hy' : y' ⋙ curvesProjectionOver B hZ = Over.map U.hom := hy
  let G := y'.obj (Over.mk (𝟙 U.left))
  have hG := CurveFamily.bijective_algebraMap_fibre_of_isGrcDimOneFamily
    (y.obj (Over.mk (𝟙 U.left))).property
  obtain ⟨hclopen, -, -⟩ := G.isClopen_fibreGenusLocus_and_pairwise_disjoint_and_iUnion_eq_univ hG
  have hchar : ∀ (T : BigFppfOver B U.left.1 U.left.2) (t : T ⟶ Over.mk (𝟙 U.left)),
      CurveFamily.HasFieldPointFibreGenus B hZ (y'.obj T) g ↔
        Set.range (Space.pointsMap B integerBase hZ (schemeSpace (y'.obj T).base).obj
          (schemeSpaceMap (y'.map t).baseMap).hom) ⊆ CurveFamily.fibreGenusLocus B hZ G g := by
    intro T t
    exact hasFieldPointFibreGenus_iff_range_pointsMap_subset
      (y.obj (Over.mk (𝟙 U.left))).property (y.obj T).property (y'.map t) g
  obtain ⟨V, hV, hVc, hVlocus⟩ := exists_open_over_of_points
    (Q := fun F => CurveFamily.HasFieldPointFibreGenus B hZ F g) U y' hy'
    (CurveFamily.fibreGenusLocus B hZ G g) (hclopen g).isOpen hchar
  exact ⟨V, hV, hVc (hclopen g).isClosed, hVlocus⟩

/-- **`Curves^{grc,1}_g ⊂ Curves^{grc,1}` is an open and closed substack** (Stacks 0E1K): the
condition is invariant under isomorphism, and the inclusion is representable by algebraic
spaces, an open immersion and a closed immersion (Stacks 04XB, 04YL). -/
theorem curvesGrcDimOneOfGenusInclusion_isOpenImmersion_and_isClosedImmersion (g : ℕ) :
    (IsGrcDimOneFibreGenus B hZ g).IsClosedUnderIsomorphisms ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesGrcDimOneOfGenusInclusion B hZ g).hom ∧
      Stack.IsOpenImmersion B integerBase hZ (curvesGrcDimOneOfGenusInclusion B hZ g) ∧
      Stack.IsClosedImmersion B integerBase hZ (curvesGrcDimOneOfGenusInclusion B hZ g) := by
  have hiso : (IsGrcDimOneFibreGenus B hZ g).IsClosedUnderIsomorphisms :=
    ⟨fun e h => isGrcDimOneFibreGenus_of_hom e.inv h⟩
  have hopen : Stack.HasOpenObjectPropertyLocus B integerBase hZ (curvesGrcDimOne B hZ).val
      (IsGrcDimOneFibreGenus B hZ g) := fun U y hy =>
    (exists_clopen_over_isGrcDimOneFibreGenus g U y hy).imp fun _ h => ⟨h.1, h.2.2⟩
  have hclosed : Stack.HasClosedLocus B integerBase hZ
      (curvesGrcDimOneOfGenusInclusion B hZ g).hom := fun U y hy => by
    obtain ⟨V, -, hVc, hVlocus⟩ := exists_clopen_over_isGrcDimOneFibreGenus g U y hy
    exact ⟨V, hVc, fun T => (hVlocus T).trans
      (Stack.image_twoFibreProductFst_objectPropertyInclusion B integerBase hZ
        (curvesGrcDimOne B hZ).val (IsGrcDimOneFibreGenus B hZ g) hiso U y hy T).symm⟩
  have h := Stack.isOpenImmersion_and_isRepresentableByAlgebraicSpaces_of_hasOpenLocus
    B integerBase hZ (curvesGrcDimOneOfGenusInclusion B hZ g)
    (Stack.full_objectPropertyInclusion B integerBase hZ (curvesGrcDimOne B hZ).val
      (IsGrcDimOneFibreGenus B hZ g))
    (Stack.faithful_objectPropertyInclusion B integerBase hZ (curvesGrcDimOne B hZ).val
      (IsGrcDimOneFibreGenus B hZ g))
    (Stack.hasOpenLocus_objectPropertyInclusion B integerBase hZ (curvesGrcDimOne B hZ).val
      (IsGrcDimOneFibreGenus B hZ g) hiso hopen)
  have h' := Stack.isClosedImmersion_and_isRepresentableByAlgebraicSpaces_of_hasClosedLocus
    B integerBase hZ (curvesGrcDimOneOfGenusInclusion B hZ g)
    (Stack.full_objectPropertyInclusion B integerBase hZ (curvesGrcDimOne B hZ).val
      (IsGrcDimOneFibreGenus B hZ g))
    (Stack.faithful_objectPropertyInclusion B integerBase hZ (curvesGrcDimOne B hZ).val
      (IsGrcDimOneFibreGenus B hZ g)) hclosed
  exact ⟨hiso, h.2, h.1, h'.1⟩

/-- **`Curves^{grc,1} = ∐_{g ≥ 0} Curves^{grc,1}_g`, on the base of an object.** For a family
`X → S` in `Curves^{grc,1}`, the loci of `S` where the fibres have genus `g` are open and closed,
pairwise disjoint and cover `S`; and a family in `Curves^{grc,1}` mapping to `X` lies in
`Curves^{grc,1}_g` exactly when its base maps into the locus of `g`. -/
theorem curvesGrcDimOne_fibreGenusLocus (X : (IsGrcDimOneFamily B hZ).FullSubcategory) :
    (∀ g, IsClopen (CurveFamily.fibreGenusLocus B hZ X.obj g)) ∧
      Pairwise (fun g g' => Disjoint (CurveFamily.fibreGenusLocus B hZ X.obj g)
        (CurveFamily.fibreGenusLocus B hZ X.obj g')) ∧
      (⋃ g, CurveFamily.fibreGenusLocus B hZ X.obj g) = Set.univ ∧
      ∀ (g : ℕ) (F : (IsGrcDimOneFamily B hZ).FullSubcategory) (a : F ⟶ X),
        (IsGrcDimOneFibreGenus B hZ g F ↔
          Set.range (Space.pointsMap B integerBase hZ (schemeSpace F.obj.base).obj
            (schemeSpaceMap a.hom.baseMap).hom) ⊆ CurveFamily.fibreGenusLocus B hZ X.obj g) := by
  have hX := CurveFamily.bijective_algebraMap_fibre_of_isGrcDimOneFamily X.property
  obtain ⟨h1, h2, h3⟩ := X.obj.isClopen_fibreGenusLocus_and_pairwise_disjoint_and_iUnion_eq_univ hX
  refine ⟨h1, h2, h3, fun g F a => ?_⟩
  exact hasFieldPointFibreGenus_iff_range_pointsMap_subset X.property F.property a.hom g

/-! ### Parts (1) and (2) -/

/-- The classifying morphism of a family of curves factors through `Curves^{grc,1}_g` exactly when
the family is in `Curves^{grc,1}` with every fibre over a field of genus `g`: a scheme-valued
point `y` of `Curves` over `U` lifts along `Curves^{grc,1}_g ⟶ Curves^{grc,1} ⟶ Curves` exactly
when the family `y(U)` it classifies has the two properties, which pass to its base changes
`y(T)`. -/
theorem factors_curvesGrcDimOneOfGenus_iff_hasFibreGenus (g : ℕ)
    (U : BigFppfOver B integerBase hZ) (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ) :
    (∃ z : BigFppfOver B U.left.1 U.left.2 ⥤ (IsGrcDimOneFibreGenus B hZ g).FullSubcategory,
        z ⋙ (IsGrcDimOneFibreGenus B hZ g).ι ⋙ (IsGrcDimOneFamily B hZ).ι = y) ↔
      IsGrcDimOneFamily B hZ (y.obj (Over.mk (𝟙 U.left))) ∧
        CurveFamily.HasFieldPointFibreGenus B hZ (y.obj (Over.mk (𝟙 U.left))) g := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨(z.obj _).obj.property, (z.obj _).property⟩
  · rintro ⟨h1, h2⟩
    have hall : ∀ T, IsGrcDimOneFamily B hZ (y.obj T) := fun T =>
      CurveFamily.isGrcDimOneFamily_of_hom (y.map (Over.homMk T.hom (by simp))) h1
    have hall' : ∀ T, IsGrcDimOneFibreGenus B hZ g (((IsGrcDimOneFamily B hZ).lift y hall).obj T) :=
      fun T => CurveFamily.hasFieldPointFibreGenus_of_hom (y.map (Over.homMk T.hom (by simp))) h2
    exact ⟨(IsGrcDimOneFibreGenus B hZ g).lift ((IsGrcDimOneFamily B hZ).lift y hall) hall', rfl⟩

/-- **Stacks 0E1K, part (1).** The classifying morphism `S → Curves` of a family of curves
`f : X → S` factors through `Curves^{grc,1}_g` exactly when the geometric fibres of `f` are
reduced, connected and of dimension `1` and `R¹f_*𝒪_X` is a locally free `𝒪_S`-module of rank
`g` (`AlgebraicGeometry.CurveFamily.HasGenus`): a scheme-valued point `y` of `Curves` over `U`
lifts along `Curves^{grc,1}_g ⟶ Curves^{grc,1} ⟶ Curves` exactly when the family `y(U)` it
classifies has these properties. -/
theorem factors_curvesGrcDimOneOfGenus_iff (g : ℕ) (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ)
    (_hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom) :
    (∃ z : BigFppfOver B U.left.1 U.left.2 ⥤ (IsGrcDimOneFibreGenus B hZ g).FullSubcategory,
        z ⋙ (IsGrcDimOneFibreGenus B hZ g).ι ⋙ (IsGrcDimOneFamily B hZ).ι = y) ↔
      IsGrcDimOneFamily B hZ (y.obj (Over.mk (𝟙 U.left))) ∧
        CurveFamily.HasGenus B hZ (y.obj (Over.mk (𝟙 U.left))) g := by
  rw [factors_curvesGrcDimOneOfGenus_iff_hasFibreGenus]
  exact and_congr_right fun h =>
    (y.obj _).hasFieldPointFibreGenus_iff_hasGenus_of_bijective_algebraMap_fibre
      (CurveFamily.bijective_algebraMap_fibre_of_isGrcDimOneFamily h) g

/-- **Stacks 0E1K, part (2).** Let `X` be a proper scheme of dimension at most one over a field
`k`. The classifying morphism `Spec k → Curves` of `X` factors through `Curves^{grc,1}_g` exactly
when `X` is geometrically reduced (Stacks 035V), geometrically connected, of dimension `1`, and
of genus `g` (Stacks 0BY7): a scheme-valued point `y` of `Curves` over `U` with `y(U) ≅ X` lifts
along `Curves^{grc,1}_g ⟶ Curves^{grc,1} ⟶ Curves` exactly when `X` has these properties. -/
theorem factors_curvesGrcDimOneOfGenus_over_field_iff (g : ℕ) {k : Type u} [Field k]
    (hk : B.Contains (Spec (.of k))) (X : Over (Spec (.of k))) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ)
    (_hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom)
    (e : y.obj (Over.mk (𝟙 U.left)) ≅ curveFamilyOfScheme X B hZ hk hdim) :
    (∃ z : BigFppfOver B U.left.1 U.left.2 ⥤ (IsGrcDimOneFibreGenus B hZ g).FullSubcategory,
        z ⋙ (IsGrcDimOneFibreGenus B hZ g).ι ⋙ (IsGrcDimOneFamily B hZ).ι = y) ↔
      IsGeometricallyReducedOver X.hom ∧ GeometricallyConnected X.hom ∧
        topologicalKrullDim X.left = 1 ∧ genus X.hom = g := by
  rw [factors_curvesGrcDimOneOfGenus_iff_hasFibreGenus]
  have htr : (IsGrcDimOneFamily B hZ (y.obj (Over.mk (𝟙 U.left))) ∧
        CurveFamily.HasFieldPointFibreGenus B hZ (y.obj (Over.mk (𝟙 U.left))) g) ↔
      (IsGrcDimOneFamily B hZ (curveFamilyOfScheme X B hZ hk hdim) ∧
        CurveFamily.HasFieldPointFibreGenus B hZ (curveFamilyOfScheme X B hZ hk hdim) g) :=
    ⟨fun h => ⟨CurveFamily.isGrcDimOneFamily_of_hom e.inv h.1,
        CurveFamily.hasFieldPointFibreGenus_of_hom e.inv h.2⟩,
      fun h => ⟨CurveFamily.isGrcDimOneFamily_of_hom e.hom h.1,
        CurveFamily.hasFieldPointFibreGenus_of_hom e.hom h.2⟩⟩
  rw [htr, isGrcDimOneFamily_curveFamilyOfScheme_iff hk X hdim,
    hasFieldPointFibreGenus_curveFamilyOfScheme_iff hk X hdim g, and_assoc, and_assoc]

/-! ### Stacks 0E1K -/

/-- **Stacks 0E1K.** There is a decomposition into open and closed substacks
`Curves^{grc,1} = ∐_{g ≥ 0} Curves^{grc,1}_g`, where `Curves^{grc,1}` is the stack of families
of curves whose geometric fibres are reduced, connected and of dimension `1`
(`AlgebraicGeometry.curvesGrcDimOne`) and `Curves^{grc,1}_g` its full subcategory
`AlgebraicGeometry.curvesGrcDimOneOfGenus`:

* each `Curves^{grc,1}_g ⊂ Curves^{grc,1}` is an open and closed substack — strictly full, with
  inclusion representable by algebraic spaces, an open immersion and a closed immersion;
* they decompose `Curves^{grc,1}`: over the base `S` of every family in `Curves^{grc,1}` their
  loci are open and closed, pairwise disjoint and cover `S`, and a family mapping to it lies in
  `Curves^{grc,1}_g` exactly when its base maps into the locus of `g`;
* (1) the classifying morphism `S → Curves` of a family of curves `f : X → S` factors through
  `Curves^{grc,1}_g` exactly when the geometric fibres of `f` are reduced, connected, of
  dimension `1` and `R¹f_*𝒪_X` is a locally free `𝒪_S`-module of rank `g`;
* (2) for a proper scheme `X` over a field `k` with `dim(X) ≤ 1`, the classifying morphism
  `Spec(k) → Curves` factors through `Curves^{grc,1}_g` exactly when `X` is geometrically
  reduced, geometrically connected, of dimension `1` and of genus `g`. -/
@[stacks 0E1K "the decomposition Curves^{grc,1} = ∐_g Curves^{grc,1}_g into open and closed \
substacks (each inclusion representable, an open and a closed immersion; on the base of every \
object the genus loci are clopen, disjoint and covering), with the characterizations (1) and (2)"]
theorem curvesGrcDimOne_genus_decomposition :
    (∀ g : ℕ, (IsGrcDimOneFibreGenus B hZ g).IsClosedUnderIsomorphisms ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesGrcDimOneOfGenusInclusion B hZ g).hom ∧
      Stack.IsOpenImmersion B integerBase hZ (curvesGrcDimOneOfGenusInclusion B hZ g) ∧
      Stack.IsClosedImmersion B integerBase hZ (curvesGrcDimOneOfGenusInclusion B hZ g)) ∧
    (∀ X : (IsGrcDimOneFamily B hZ).FullSubcategory,
      (∀ g, IsClopen (CurveFamily.fibreGenusLocus B hZ X.obj g)) ∧
      Pairwise (fun g g' => Disjoint (CurveFamily.fibreGenusLocus B hZ X.obj g)
        (CurveFamily.fibreGenusLocus B hZ X.obj g')) ∧
      (⋃ g, CurveFamily.fibreGenusLocus B hZ X.obj g) = Set.univ ∧
      ∀ (g : ℕ) (F : (IsGrcDimOneFamily B hZ).FullSubcategory) (a : F ⟶ X),
        (IsGrcDimOneFibreGenus B hZ g F ↔
          Set.range (Space.pointsMap B integerBase hZ (schemeSpace F.obj.base).obj
            (schemeSpaceMap a.hom.baseMap).hom) ⊆ CurveFamily.fibreGenusLocus B hZ X.obj g)) ∧
    (∀ (g : ℕ) (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤ (IsGrcDimOneFibreGenus B hZ g).FullSubcategory,
          z ⋙ (IsGrcDimOneFibreGenus B hZ g).ι ⋙ (IsGrcDimOneFamily B hZ).ι = y) ↔
        IsGrcDimOneFamily B hZ (y.obj (Over.mk (𝟙 U.left))) ∧
          CurveFamily.HasGenus B hZ (y.obj (Over.mk (𝟙 U.left))) g)) ∧
    (∀ (g : ℕ) (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
      (X : Over (Spec (.of k))) [IsProper X.hom] (hdim : topologicalKrullDim X.left ≤ 1)
      (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      (y.obj (Over.mk (𝟙 U.left)) ≅ curveFamilyOfScheme X B hZ hk hdim) →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤ (IsGrcDimOneFibreGenus B hZ g).FullSubcategory,
          z ⋙ (IsGrcDimOneFibreGenus B hZ g).ι ⋙ (IsGrcDimOneFamily B hZ).ι = y) ↔
        IsGeometricallyReducedOver X.hom ∧ GeometricallyConnected X.hom ∧
          topologicalKrullDim X.left = 1 ∧ genus X.hom = g)) :=
  ⟨curvesGrcDimOneOfGenusInclusion_isOpenImmersion_and_isClosedImmersion,
    curvesGrcDimOne_fibreGenusLocus,
    factors_curvesGrcDimOneOfGenus_iff,
    fun g _ _ hk X _ hdim U y hy e =>
      factors_curvesGrcDimOneOfGenus_over_field_iff g hk X hdim U y hy e⟩

end AlgebraicGeometry

end
