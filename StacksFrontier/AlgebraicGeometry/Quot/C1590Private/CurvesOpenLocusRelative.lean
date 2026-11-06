module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable

/-!
# Condition (o) of Stacks 0E0E inside an open substack of curves

The proofs of Stacks 0E6U and 0E70 begin "by the discussion in Section 0E0E it suffices to look at
families of prestable curves": to show that a property `P` of families of curves satisfies
condition (o) of Stacks 0E0E it is enough that `P` implies a property `Q` which satisfies
condition (o), and that over the base of every family `G` with `Q` there is an open set of points
describing `P` on every family mapping to `G`. This file proves that reduction,
`AlgebraicGeometry.C1590Private.IsOpenCurvesLocus.of_le`, by restricting a family to the open
subscheme of its base over which it has `Q`.

## Main definitions

* `AlgebraicGeometry.C1590Private.CurveFamily.restrict`: the base change of a family of curves
  along a morphism of the site into its base, with its morphism
  `AlgebraicGeometry.C1590Private.CurveFamily.restrictHom` to the family.

## Main results

* `AlgebraicGeometry.C1590Private.CurveFamily.exists_hom_restrict`: a morphism of families
  whose morphism of bases factors through `j` factors through the restriction along `j`.
* `AlgebraicGeometry.C1590Private.IsOpenCurvesLocus.of_le`: the reduction of condition (o) to
  the families with a property already satisfying it.
* `AlgebraicGeometry.C1590Private.isOpen_preimage_pointsToScheme`: an open set of points of a
  base scheme gives an open set of points of its algebraic space.

## References

* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 0E6U](https://stacks.math.columbia.edu/tag/0E6U)
* [Stacks Project, Tag 0E70](https://stacks.math.columbia.edu/tag/0E70)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.C1590Private

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- Pullbacks of presheaves on the big fppf site over `Spec ℤ`, given directly: instance search
for them times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_CurvesOpenLocusRelative :
    HasPullbacks ((BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_CurvesOpenLocusRelative
    {X Y Z : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_CurvesOpenLocusRelative (B := B) (hZ := hZ)).has_limit _

/-- Discrete limits of presheaves on the big fppf site over `Spec ℤ`, given directly for the
same reason. -/
local instance (priority := high) hasLimitsOfShape_discrete_presheaf_CurvesOpenLocusRelative
    (J : Type) : HasLimitsOfShape (Discrete J) ((BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

namespace CurveFamily

/-- The base change of a family of curves `G` along a morphism `j : V ⟶ S` of the site into its
base: the family `G ×_S V ⟶ V`. -/
def restrict (G : AlgebraicGeometry.CurveFamily B hZ) {V : BigFppfOver B integerBase hZ}
    (j : V ⟶ G.base) : AlgebraicGeometry.CurveFamily B hZ :=
  G.ofIsPullback B hZ j _ _ (AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ G.toBase
    (schemeSpaceMap j))

/-- The morphism of families of curves from the base change of `G` along `j` to `G`; its
morphism of bases is `j`. -/
def restrictHom (G : AlgebraicGeometry.CurveFamily B hZ) {V : BigFppfOver B integerBase hZ}
    (j : V ⟶ G.base) : restrict G j ⟶ G :=
  G.homOfIsPullback B hZ j _ _ (AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ
    G.toBase (schemeSpaceMap j))

/-- The morphism of bases underlying the canonical morphism `restrictHom G j` from the
restriction of `G` along `j` is `j` itself. -/
@[simp]
theorem restrictHom_baseMap (G : AlgebraicGeometry.CurveFamily B hZ)
    {V : BigFppfOver B integerBase hZ} (j : V ⟶ G.base) : (restrictHom G j).baseMap = j :=
  rfl

/-- **Morphisms into a restriction.** A morphism of families of curves `a : F ⟶ G` whose morphism
of bases factors as `k ≫ j` factors through the restriction of `G` along `j`, with morphism of
bases `k`: the cartesian square of `a` is the paste of the square of the factorization with the
cartesian square of the restriction. -/
theorem exists_hom_restrict {F G : AlgebraicGeometry.CurveFamily B hZ} (a : F ⟶ G)
    {V : BigFppfOver B integerBase hZ} (j : V ⟶ G.base) (k : F.base ⟶ V)
    (hk : k ≫ j = a.baseMap) : ∃ a' : F ⟶ restrict G j, a'.baseMap = k := by
  have sq := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ G.toBase (schemeSpaceMap j)
  have hw : a.totalMap ≫ G.toBase = (F.toBase ≫ schemeSpaceMap k) ≫ schemeSpaceMap j := by
    rw [a.cartesian.w, Category.assoc, ← hk]
    rfl
  refine ⟨⟨k, sq.lift a.totalMap (F.toBase ≫ schemeSpaceMap k) hw, ?_⟩, rfl⟩
  refine IsPullback.of_right (h₁₂ := ObjectProperty.homMk (pullback.fst G.toBase.hom
    (schemeSpaceMap j).hom)) (h₂₂ := schemeSpaceMap j) (v₁₃ := G.toBase) ?_ (sq.lift_snd _ _ _) sq
  convert a.cartesian using 1
  all_goals first | exact sq.lift_fst _ _ _ | (rw [← hk]; rfl)

end CurveFamily

/-- An open set of points of the scheme of a site object is open for the point topology of the
represented algebraic space, after pulling back along the comparison bijection. -/
theorem isOpen_preimage_pointsToScheme (U : BigFppfOver B integerBase hZ)
    {Ω : Set ((BigFppfOver.toScheme B integerBase hZ).obj U)} (hΩ : IsOpen Ω) :
    IsOpen (Space.pointsToScheme B integerBase hZ U ⁻¹' Ω) := by
  rw [Space.isOpen_pointTopology_yoneda_iff_isOpen_image,
    Set.image_preimage_eq _ (Space.surjective_pointsToScheme B integerBase hZ U)]
  exact hΩ

/-- **Condition (o) inside an open substack** (the reduction of Section 0E0E used in the proofs
of Stacks 0E6U and 0E70). Let `Q` be a property of families of curves satisfying condition (o)
and `P` a property implying `Q`. Suppose that every family `G` with `Q` has an open set of points
of its base such that a family mapping to `G` has `P` exactly when its morphism of bases lands in
that set. Then `P` satisfies condition (o). -/
theorem IsOpenCurvesLocus.of_le {P Q : ObjectProperty (AlgebraicGeometry.CurveFamily B hZ)}
    (hQ : IsOpenCurvesLocus B hZ Q) (hPQ : ∀ F, P F → Q F)
    (hrel : ∀ G : AlgebraicGeometry.CurveFamily B hZ, Q G →
      ∃ Ω : Set (Space.points B integerBase hZ (schemeSpace G.base).obj), IsOpen Ω ∧
        ∀ (F : AlgebraicGeometry.CurveFamily B hZ) (a : F ⟶ G),
          P F ↔ Set.range (Space.pointsMap B integerBase hZ (schemeSpace F.base).obj
            (schemeSpaceMap a.baseMap).hom) ⊆ Ω) :
    IsOpenCurvesLocus B hZ P := by
  refine IsOpenCurvesLocus.of_points fun G => ?_
  obtain ⟨W, hW, hWchar⟩ := hQ G
  obtain ⟨V, j, hj, e, he⟩ : ∃ (V : BigFppfOver B integerBase hZ) (j : V ⟶ G.base),
      AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map j) ∧
      ∃ e : yoneda.obj V ≅ W.toFunctor, e.hom ≫ W.ι = yoneda.map j := by
    have key : ∀ (U' : BigFppfOver B integerBase hZ) (W' : Subfunctor (yoneda.obj U')),
        Space.IsOpenSubspace B integerBase hZ W' →
        ∃ (V : BigFppfOver B integerBase hZ) (j : V ⟶ U'),
          AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map j) ∧
          ∃ e : yoneda.obj V ≅ W'.toFunctor, e.hom ≫ W'.ι = yoneda.map j := by
      intro U' W' hW'
      let h := hW'.2.rep.isPullback (𝟙 (yoneda.obj U'))
      let eMap := hW'.2.rep.fst (𝟙 (yoneda.obj U'))
      have : IsIso eMap := h.isIso_fst_of_isIso
      exact ⟨_, hW'.2.rep.snd (𝟙 (yoneda.obj U')), hW'.2.property_snd (𝟙 (yoneda.obj U')),
        asIso eMap, by simpa [eMap] using h.w⟩
    exact key G.base W hW
  have hXG := (schemeSpace G.base).property
  have hjo : Space.IsOpenImmersion B integerBase hZ (yoneda.map j) :=
    Space.isOpenImmersion_yoneda_map B integerBase hZ j hj
  have hinj : Function.Injective (Space.pointsMap B integerBase hZ (yoneda.obj V) (yoneda.map j)) :=
    Space.injective_pointsMap_of_isImmersion B integerBase hZ hXG _
      (Space.isImmersion_of_isOpenImmersion B integerBase hZ hjo)
  -- a morphism of bases factoring through `W` factors through `j`
  have hgen : ∀ {U' V' A : BigFppfOver B integerBase hZ} (W' : Subfunctor (yoneda.obj U'))
      (j' : V' ⟶ U') (e' : yoneda.obj V' ≅ W'.toFunctor) (_he' : e'.hom ≫ W'.ι = yoneda.map j')
      (b : A ⟶ U'), (∃ t : yoneda.obj A ⟶ W'.toFunctor, t ≫ W'.ι = yoneda.map b) →
        ∃ k : A ⟶ V', k ≫ j' = b := by
    intro U' V' A W' j' e' he' b ⟨t, ht⟩
    have he'' : e'.inv ≫ yoneda.map j' = W'.ι := by
      rw [← he', ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    refine ⟨Yoneda.fullyFaithful.preimage (t ≫ e'.inv), yoneda.map_injective ?_⟩
    rw [Functor.map_comp, Yoneda.fullyFaithful.map_preimage, Category.assoc, he'', ht]
  have hfac : ∀ {A : BigFppfOver B integerBase hZ} (b : A ⟶ G.base),
      (∃ t : yoneda.obj A ⟶ W.toFunctor, t ≫ W.ι = yoneda.map b) →
        ∃ k : A ⟶ V, k ≫ j = b :=
    fun b hb => hgen (U' := G.base) W j e he b hb
  obtain ⟨Ω', hΩ', hchar'⟩ := hrel _ ((hWchar _ (CurveFamily.restrictHom G j)).2 ⟨e.hom, he⟩)
  refine ⟨Space.pointsMap B integerBase hZ (yoneda.obj V) (yoneda.map j) '' Ω',
    Space.isOpenMap_pointsMap_of_isOpenImmersion B integerBase hZ _ hjo _ hΩ', fun F a => ?_⟩
  have hrange : ∀ (k : F.base ⟶ V), k ≫ j = a.baseMap →
      Set.range (Space.pointsMap B integerBase hZ (schemeSpace F.base).obj
          (schemeSpaceMap a.baseMap).hom) =
        Space.pointsMap B integerBase hZ (yoneda.obj V) (yoneda.map j) ''
          Set.range (Space.pointsMap B integerBase hZ (yoneda.obj F.base) (yoneda.map k)) := by
    intro k hk
    show Set.range (Space.pointsMap B integerBase hZ (yoneda.obj F.base)
      (yoneda.map a.baseMap)) = _
    rw [← hk, Functor.map_comp, Space.pointsMap_comp, Set.range_comp]
  constructor
  · intro hP
    obtain ⟨k, hk⟩ := hfac a.baseMap ((hWchar F a).1 (hPQ F hP))
    obtain ⟨a', ha'⟩ := CurveFamily.exists_hom_restrict a j k hk
    rw [hrange k hk]
    refine Set.image_mono ?_
    have := (hchar' F a').1 hP
    rwa [ha'] at this
  · intro hsub
    have hW' : Set.range (Space.pointsMap B integerBase hZ (schemeSpace F.base).obj
        (schemeSpaceMap a.baseMap).hom) ⊆
          Set.range (Space.pointsMap B integerBase hZ W.toFunctor W.ι) := by
      refine hsub.trans ?_
      rintro _ ⟨x, -, rfl⟩
      refine ⟨Space.pointsMap B integerBase hZ _ e.hom x, ?_⟩
      rw [← Function.comp_apply (f := Space.pointsMap B integerBase hZ _ W.ι),
        ← Space.pointsMap_comp, he]
    obtain ⟨k, hk⟩ := hfac a.baseMap ((Space.factorsThrough_openSubspace_iff_points B
      integerBase hZ hXG (schemeSpace F.base).property W hW _).2 hW')
    obtain ⟨a', ha'⟩ := CurveFamily.exists_hom_restrict a j k hk
    refine (hchar' F a').2 ?_
    rw [ha']
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz, hzy⟩ := hsub ((hrange k hk).symm ▸ ⟨_, ⟨y, rfl⟩, rfl⟩ :
      Space.pointsMap B integerBase hZ (yoneda.obj V) (yoneda.map j)
        (Space.pointsMap B integerBase hZ _ (yoneda.map k) y) ∈ _)
    rwa [hinj hzy] at hz

end AlgebraicGeometry.C1590Private

end
