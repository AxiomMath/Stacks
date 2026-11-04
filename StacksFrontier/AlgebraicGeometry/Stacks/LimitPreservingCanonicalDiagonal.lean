module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingCanonicalCell
public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCatGroupoid
public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCatNatTrans
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatSquareComparisonDiagonal

/-!
# Condition (2) of Stacks 0CMW through the diagonal of the canonical square

`AlgebraicGeometry.Stack.IsFullyFaithfulOnAffineLimits` is condition (2) of Stacks 0CMW: at every
directed limit of affines the canonical functor `colim 𝒳_{Uᵢ} ⟶ 𝒳_U ×_{𝒴_U} colim 𝒴_{Uᵢ}` is
fully faithful. That functor is the comparison out of
`AlgebraicGeometry.Stack.canonicalSquare`, so the category-theoretic criterion of Stacks 0CMW
(`CategoryTheory.Limits.CategoricalPullback.fullyFaithful_squareComparison_iff`, in the `Cat`-level
form `CategoryTheory.Cat.fullyFaithful_toCategoricalPullbackFunctor_iff`) applies to it directly,
and this file carries it over: condition (2) holds exactly when, at every directed limit of
affines, the comparison of the *square of relative diagonals* of the canonical square is an
equivalence.

Both directions are available because the pinned data `T`, `H`, `η` that condition (2) quantifies
over is determined by `f`: `T` and `H` are pinned outright, and `η` is pinned at the colimit
generators, which determines it because every object of a filtered colimit in `Cat` *is* the image
of an object of a stage (`CategoryTheory.Cat.natIso_ext_of_colimit`).

The two corners the criterion needs to be groupoids are `𝒳_U` — the fibre of a category fibred in
groupoids — and `colim 𝒴_{Uᵢ}`, which is a filtered colimit of split fibres of a category fibred
in groupoids; the second is
`CategoryTheory.Cat.isGroupoid_colimit`.

What is *not* here is the identification of that diagonal comparison with the comparison of the
canonical square of the diagonal 1-morphism `Δ : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳`, which is what turns this into the
equivalence of conditions (1) and (2) of Stacks 0CMW. That identification needs the fibre of a
2-fibre product to be the 2-fibre product of the fibres (Stacks 02XI) and filtered colimits of
categories to commute with 2-fibre products, which are proved in
`StacksFrontier.CategoryTheory.TwoFibreProduct.OverFibres` and
`StacksFrontier.CategoryTheory.Limits.FilteredColimitCatTwoFibreProductEquivalence`.

## Main results

* `AlgebraicGeometry.Stack.fullyFaithful_canonicalSquare_of_isFullyFaithfulOnAffineLimits`: the
  square whose comparison condition (2) asserts to be fully faithful is
  `AlgebraicGeometry.Stack.canonicalSquare`, the pinned data being determined.
* `Stack.isFullyFaithfulOnAffineLimits_iff_isEquivalence_squareDiagonalComparison`: condition (2)
  of Stacks 0CMW holds exactly when the canonical square has, at every directed limit of affines,
  an equivalence for the comparison of its square of relative diagonals.
* `AlgebraicGeometry.Stack.isGroupoid_colimit_fiberDiagram`: the colimit of the stage fibres is a
  groupoid, one of the two corners the criterion needs.
* `AlgebraicGeometry.Stack.isLimitPreserving_iff_isTwoFibreProduct_canonicalSquare`: the same
  determinacy on the 2-cartesian clause, so that condition (1) of Stacks 0CMW — limit
  preservation of the diagonal 1-morphism — is likewise a property of
  `AlgebraicGeometry.Stack.canonicalSquare` alone.

## References

* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
* [Stacks Project, Tag 0CMR](https://stacks.math.columbia.edu/tag/0CMR)
* [Stacks Project, Tag 04Z7](https://stacks.math.columbia.edu/tag/04Z7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Opposite

namespace AlgebraicGeometry.Stack

universe u v w uX vX uC vC wC

attribute [local implicit_reducible] Bicategory.InducedBicategory Functor.Fiber
  Functor.Fiber.fiberInclusion Functor.SplitFiber.restrict Deformation.Artin.fiberDiagram
  Functor.splitPresheaf Cat.asSmallFunctor

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : CatFiberedInGroupoids.{u, vX, u + 1, uX} (BigFppfOver B S hS)}
  {I : Type v} [Category.{w} I]

/-- The nerve of the strict diagram of split fibres has a colimit: simplicial sets have all
colimits, and the index category is small enough to shrink to. -/
lemma hasColimit_fiberDiagram_comp_nerveFunctor (𝒵 : CatFiberedInGroupoids.{u, vX, u + 1, uX}
    (BigFppfOver B S hS)) (E : I ⥤ BigFppfOver B S hS) :
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    HasColimit (Deformation.Artin.fiberDiagram 𝒵.val.p E ⋙
      CategoryTheory.nerveFunctor.{max v w vX (u + 1) uX u, max v w vX (u + 1) uX u}) := by
  let : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  let : HasColimitsOfSize.{w, v} SSet.{max v w vX (u + 1) uX u} :=
    hasColimitsOfSizeShrink.{w, v, max v w vX (u + 1) uX u, max v w vX (u + 1) uX u} _
  infer_instance

/-- **The colimit of the stage fibres of a category fibred in groupoids is a groupoid.** Each
stage is a split fibre, whose morphisms are morphisms of a fibre of a category fibred in
groupoids, and the index category of the colimit is filtered. -/
lemma isGroupoid_colimit_fiberDiagram (𝒵 : CatFiberedInGroupoids.{u, vX, u + 1, uX}
    (BigFppfOver B S hS)) (E : I ⥤ BigFppfOver B S hS) [IsCofiltered I] :
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    IsGroupoid ↑(colimit (Deformation.Artin.fiberDiagram 𝒵.val.p E)) := by
  let : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  have := hasColimit_fiberDiagram_comp_nerveFunctor B S hS 𝒵 E
  have (V : BigFppfOver B S hS) : IsGroupoid (𝒵.val.p.Fiber V) := 𝒵.2.fiber_isGroupoid V
  refine Cat.isGroupoid_colimit.{max v w vX (u + 1) uX u, v, w}
    (Deformation.Artin.fiberDiagram 𝒵.val.p E) fun j => ?_
  exact inferInstanceAs
    (IsGroupoid (AsSmall.{max v w} (𝒵.val.p.SplitFiber (E.obj j.unop))))

/-- A morphism of a universe-lifted category is determined by its image under the lift, the lift
and its inverse being strictly mutually inverse. -/
lemma asSmall_down_map_injective {C : Type uC} [Category.{vC} C] {A A' : AsSmall.{wC} C}
    {g g' : A ⟶ A'} (e : AsSmall.down.map g = AsSmall.down.map g') : g = g' :=
  congrArg (AsSmall.up.{vC, uC, wC} (C := C)).map e

/-- A morphism of a universe-lifted category is determined by its image under the lift. This is
the module-local name of `asSmall_down_map_injective`. -/
private alias asSmall_down_map_inj := asSmall_down_map_injective

/-- Every object of a stage of the strict diagram of split fibres of Stacks 004A is the universe
lift of an object of that split fibre. -/
private lemma exists_asSmall_up_obj (𝒵 : CatFiberedInGroupoids.{u, vX, u + 1, uX}
    (BigFppfOver B S hS)) (E : I ⥤ BigFppfOver B S hS) (j : Iᵒᵖ) :
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    ∀ a : ↑((Deformation.Artin.fiberDiagram 𝒵.val.p E).obj j),
      ∃ x : 𝒵.val.p.SplitFiber (E.obj j.unop),
        AsSmall.up.{vX, max (u + 1) uX, max v w}.obj x = a :=
  let : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  fun a => ⟨AsSmall.down.{vX, max (u + 1) uX, max v w}.obj a, rfl⟩

/-- The pinned componentwise maps `T` of the square of Stacks 0CMR are `fiberDiagramMap`. -/
private lemma eq_fiberDiagramMap_of_pinned (f : 𝒳 ⟶ 𝒴) (E : I ⥤ BigFppfOver B S hS)
    (T : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
      Deformation.Artin.fiberDiagram 𝒳.val.p E ⟶ Deformation.Artin.fiberDiagram 𝒴.val.p E)
    (hT : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
      ∀ i : I, T.app (op i) =
        (AsSmall.down ⋙ splitFiberMap B S hS f (E.obj i) ⋙ AsSmall.up).toCatHom) :
    T = fiberDiagramMap B S hS f E :=
  NatTrans.ext (funext fun j => (hT j.unop).trans (fiberDiagramMap_app B S hS f _ j.unop).symm)

/-- The pinned 2-cell `η` of the square of Stacks 0CMR is `canonicalTwoCellUp`, since it is
determined by its values at the colimit generators. -/
private lemma eq_canonicalTwoCellUp_of_pinned (f : 𝒳 ⟶ 𝒴) (E : I ⥤ BigFppfOver B S hS)
    (d : Cone E) [IsCofiltered I]
    (η : type_of% (canonicalTwoCellUp.{u, v, w, uX, vX} B S hS f E d))
    (hη : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
      ∀ (i : I) (x : 𝒳.val.p.SplitFiber (E.obj i)),
        HEq
          (AsSmall.down.map
            ((η.app ((colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E)
              (op i)).toFunctor.obj (AsSmall.up.{vX, max (u + 1) uX, max v w}.obj x))).hom))
          ((isFibredOneMorphism B S hS f).mapPullbackFiberIso x.obj (d.π.app i ≫ x.hom)).inv) :
    η = canonicalTwoCellUp B S hS f E d := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  have := hasColimit_fiberDiagram_comp_nerveFunctor B S hS 𝒳 E
  refine Cat.natIso_ext_of_colimit.{max v w vX (u + 1) uX u, v, w} η _ fun j a => ?_
  obtain ⟨x, rfl⟩ := exists_asSmall_up_obj B S hS 𝒳 E j a
  exact asSmall_down_map_inj (eq_of_heq ((hη j.unop x).trans
    (canonicalTwoCellUp_app_ι B S hS f _ _ j.unop x).symm))

/-- **The pinned data of the square of Stacks 0CMR is the canonical data.** Condition (2) of
Stacks 0CMW asserts full faithfulness of the comparison out of *some* square whose data `T`, `H`
and `η` is pinned; the pinning determines all three, so it is full faithfulness of the comparison
out of `AlgebraicGeometry.Stack.canonicalSquare`. For `η` this is where filteredness is used:
`η` is pinned only at the colimit generators, and
`CategoryTheory.Cat.natIso_ext_of_colimit` turns that into an equality. -/
theorem fullyFaithful_canonicalSquare_of_isFullyFaithfulOnAffineLimits (f : 𝒳 ⟶ 𝒴)
    (hf : IsFullyFaithfulOnAffineLimits.{u, v, w, uX, vX} B S hS f)
    (J : Type v) [Category.{w} J] [IsCofiltered J] (D : J ⥤ BigAffineFppf B S hS) (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    (Cat.toCategoricalPullbackFunctor (canonicalSquare.{u, v, w, uX, vX} B S hS f
          (D ⋙ BigAffineFppf.inclusion B S hS)
          ((BigAffineFppf.inclusion B S hS).mapCone c))).Full ∧
      (Cat.toCategoricalPullbackFunctor (canonicalSquare.{u, v, w, uX, vX} B S hS f
          (D ⋙ BigAffineFppf.inclusion B S hS)
          ((BigAffineFppf.inclusion B S hS).mapCone c))).Faithful := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  obtain ⟨T, H, η, hT, hH, hη, hfull, hfaith⟩ := hf J D c hc
  subst hH
  obtain rfl := eq_fiberDiagramMap_of_pinned B S hS f _ T hT
  obtain rfl := eq_canonicalTwoCellUp_of_pinned B S hS f _ _ η hη
  exact ⟨hfull, hfaith⟩

/-- **The pinned data of the square of Stacks 0CMR is the canonical data, on the 2-cartesian
clause.** This is the companion of
`AlgebraicGeometry.Stack.fullyFaithful_canonicalSquare_of_isFullyFaithfulOnAffineLimits` for
condition (1): limit preservation asserts that *some* square whose data `T`, `H` and `η` is
pinned is a 2-fibre product, and since the pinning determines all three it is
`AlgebraicGeometry.Stack.canonicalSquare` that is a 2-fibre product. -/
theorem isTwoFibreProduct_canonicalSquare_of_isLimitPreserving (f : 𝒳 ⟶ 𝒴)
    (hf : IsLimitPreserving.{u, v, w, uX, vX} B S hS f)
    (J : Type v) [Category.{w} J] [IsCofiltered J] (D : J ⥤ BigAffineFppf B S hS) (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    Nonempty (Bicategory.IsTwoFibreProduct
      (canonicalSquare.{u, v, w, uX, vX} B S hS f (D ⋙ BigAffineFppf.inclusion B S hS)
        ((BigAffineFppf.inclusion B S hS).mapCone c))) := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  obtain ⟨T, H, η, hT, hH, hη, hcart⟩ := hf J D c hc
  subst hH
  obtain rfl := eq_fiberDiagramMap_of_pinned B S hS f _ T hT
  obtain rfl := eq_canonicalTwoCellUp_of_pinned B S hS f _ _ η hη
  exact hcart

/-- **Stacks 0CMR is a property of the canonical square alone.** A 1-morphism is limit preserving
exactly when, at every directed limit of affine schemes over `S`,
`AlgebraicGeometry.Stack.canonicalSquare` is a 2-fibre product: one direction is the pinned data
being determinate, the other is that the canonical data is pinned data. -/
theorem isLimitPreserving_iff_isTwoFibreProduct_canonicalSquare (f : 𝒳 ⟶ 𝒴) :
    IsLimitPreserving.{u, v, w, uX, vX} B S hS f ↔
      ∀ (I : Type v) [Category.{w} I] [IsCofiltered I]
        (D : I ⥤ BigAffineFppf B S hS) (c : Cone D),
        IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c) →
        Nonempty (Bicategory.IsTwoFibreProduct
          (canonicalSquare.{u, v, w, uX, vX} B S hS f (D ⋙ BigAffineFppf.inclusion B S hS)
            ((BigAffineFppf.inclusion B S hS).mapCone c))) :=
  ⟨fun hf J _ _ D c hc =>
      isTwoFibreProduct_canonicalSquare_of_isLimitPreserving B S hS f hf J D c hc,
    isLimitPreserving_of_canonicalSquare B S hS f⟩

/-- **Condition (2) of Stacks 0CMW through the diagonal of the canonical square.** If, at every
directed limit of affine schemes over `S`, the comparison of the square of relative diagonals of
`AlgebraicGeometry.Stack.canonicalSquare` is an equivalence, then the canonical functor
`colim 𝒳_{Uᵢ} ⟶ 𝒳_U ×_{𝒴_U} colim 𝒴_{Uᵢ}` is fully faithful. -/
theorem isFullyFaithfulOnAffineLimits_of_isEquivalence_squareDiagonalComparison (f : 𝒳 ⟶ 𝒴)
    (h : ∀ (I : Type v) [Category.{w} I] [IsCofiltered I]
      (D : I ⥤ BigAffineFppf B S hS) (c : Cone D),
      IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c) →
      (Cat.squareDiagonalComparison
        (canonicalSquare.{u, v, w, uX, vX} B S hS f (D ⋙ BigAffineFppf.inclusion B S hS)
          ((BigAffineFppf.inclusion B S hS).mapCone c))).IsEquivalence) :
    IsFullyFaithfulOnAffineLimits.{u, v, w, uX, vX} B S hS f := by
  apply isFullyFaithfulOnAffineLimits_of_canonicalSquare
  intro I _ _ D c hc
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  have : IsGroupoid (𝒳.val.p.Fiber
      ((BigAffineFppf.inclusion B S hS).mapCone c).pt) :=
    𝒳.2.fiber_isGroupoid _
  have := isGroupoid_colimit_fiberDiagram B S hS 𝒴 (D ⋙ BigAffineFppf.inclusion B S hS)
  exact (Cat.fullyFaithful_toCategoricalPullbackFunctor_iff _).mpr (h I D c hc)

/-- **Condition (2) of Stacks 0CMW is the diagonal of the canonical square being an
equivalence.** The canonical functor `colim 𝒳_{Uᵢ} ⟶ 𝒳_U ×_{𝒴_U} colim 𝒴_{Uᵢ}` is fully faithful
at every directed limit of affine schemes over `S` exactly when, at every such limit, the
comparison of the square of relative diagonals of `AlgebraicGeometry.Stack.canonicalSquare` is an
equivalence.

This is the half of Stacks 0CMW that does not involve the diagonal 1-morphism
`Δ : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳`: it is the category-theoretic criterion of the source's proof, applied to the
determinate square of Stacks 0CMR. -/
@[stacks 0CMW "condition (2) as the diagonal of the canonical 0CMR square being an equivalence"]
theorem isFullyFaithfulOnAffineLimits_iff_isEquivalence_squareDiagonalComparison (f : 𝒳 ⟶ 𝒴) :
    IsFullyFaithfulOnAffineLimits.{u, v, w, uX, vX} B S hS f ↔
      ∀ (I : Type v) [Category.{w} I] [IsCofiltered I]
        (D : I ⥤ BigAffineFppf B S hS) (c : Cone D),
        IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c) →
        (Cat.squareDiagonalComparison
          (canonicalSquare.{u, v, w, uX, vX} B S hS f (D ⋙ BigAffineFppf.inclusion B S hS)
            ((BigAffineFppf.inclusion B S hS).mapCone c))).IsEquivalence := by
  refine ⟨fun hf J _ _ D c hc => ?_,
    isFullyFaithfulOnAffineLimits_of_isEquivalence_squareDiagonalComparison B S hS f⟩
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  have : IsGroupoid (𝒳.val.p.Fiber
      ((BigAffineFppf.inclusion B S hS).mapCone c).pt) :=
    𝒳.2.fiber_isGroupoid _
  have := isGroupoid_colimit_fiberDiagram B S hS 𝒴 (D ⋙ BigAffineFppf.inclusion B S hS)
  exact (Cat.fullyFaithful_toCategoricalPullbackFunctor_iff _).mp
    (fullyFaithful_canonicalSquare_of_isFullyFaithfulOnAffineLimits B S hS f hf J D c hc)

end AlgebraicGeometry.Stack

end
