module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Completion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MorphismUniquenessAlongClosedSubset
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.PointwiseEtale
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.SmoothnessOverNoetherianBase
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DiagonalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationSize
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# Morphisms out of an algebraic space with a proper modification along a closed subset

Let `S` be a scheme, let `X` be a locally Noetherian algebraic space over `S`, let `T ⊆ |X|` be
a closed subset with complementary open subspace `U ⊆ X`, and let `f : X' ⟶ X` be a proper
morphism of algebraic spaces whose base change `f⁻¹(U) ⟶ U` is an isomorphism. For an algebraic
space `W` over `S` a morphism `X ⟶ W` restricts to a morphism `X' ⟶ W` and to a morphism of the
completion `X_{/T} ⟶ W`, and the two restrictions agree on `X'_{/T}`. This file shows that a
morphism out of `X` is *determined* by that pair, which is the injectivity half of the
comparison map of Stacks 0GI3.

## Main definitions

* `AlgebraicGeometry.Space.morToModificationCompletion` is the comparison map, sending a
  morphism `X ⟶ W` to its restriction along `f` together with the induced morphism
  `X_{/T} ⟶ W`.

## Main results

* `AlgebraicGeometry.Space.morToModificationCompletion_compatible`: the comparison map lands in
  the fibre product, that is, the two components of the pair it produces induce the same
  morphism `X'_{/T} ⟶ W`.
* `AlgebraicGeometry.Space.morToModificationCompletion_injective`: **Stacks 0GI3**, injectivity
  of the comparison map.

## Implementation notes

*The completion.* `X_{/T}` is the completion of Stacks 0AIZ, the subfunctor
`AlgebraicGeometry.Space.completionSubfunctor` of sections whose point-set image lies in `T`;
`AlgebraicGeometry.Space.completionSheaf` is its fppf sheafification, to which it is
canonically isomorphic because the condition on a section is already fppf-local. A morphism
`X_{/T} ⟶ W` is therefore a morphism of subfunctors into the universe lift of `W`, and the
morphism induced by `a : X ⟶ W` is the composite of the inclusion of the subfunctor with the
universe lift of `a`. Likewise `X ∖ T` is `AlgebraicGeometry.Space.openSubspaceOfPoints`
applied to `Tᶜ`, the open subspace of Stacks 03BZ with point set `Tᶜ`, and `f⁻¹(U) ⟶ U` is the
base change `pullback.snd f` of `f` along its inclusion, as in
`AlgebraicGeometry.Space.IsModification`.

*Injectivity.* Only the hypothesis that `f⁻¹(U) ⟶ U` is an isomorphism is used, and only to
transport the agreement of two morphisms after `f` to agreement on `X ∖ T`: the two composites
with the base change `f⁻¹(U) ⟶ U` agree because the square commutes, and an isomorphism is an
epimorphism. The content is then Stacks 0GI1, which is proved here. Properness of `f` is what
makes the comparison map *surjective*; that half is not proved here, so the hypothesis is
recorded and unused, as is the hypothesis that `X'` is an algebraic space.

*The uniqueness input.* Injectivity is Stacks 0GI1: two morphisms out of a locally Noetherian
algebraic space which agree on `X ∖ T` and on `X_{/T}` are equal. The available form of Stacks
0AR7, `AlgebraicGeometry.Space.eq_of_eq_on_compl_of_completionSubfunctorMap_eq`, is that
statement for a target completed along a closed subset of its own, and it carries the source's
hypothesis that the *target* is locally Noetherian as well, which Stacks 0GI3 does not assume
of `W`. The form needed here is therefore established directly, by the same argument: equality
of morphisms out of `X` may be tested on a surjective étale atlas
`p : V ⟶ X` (`AlgebraicGeometry.Space.hom_ext_of_etale_atlas`), and the atlas may be chosen
with `V` locally Noetherian since `X` is. Write `W₀ ⊆ |V|` for the inverse image of `T`, a
closed subset, and let `E = V ×_{(p a, p b), W × W} W` be the locus in `V` where the two
composites agree. The diagonal of `W` is representable, a monomorphism and locally of finite
type — Stacks 02X4 — so `E` is an object of the site and `E ⟶ V` is a monomorphism of schemes
locally of finite type. A morphism `Z ⟶ V` factors through `E` exactly when the two composites
to `W` agree on it, so the open complement of `W₀` factors through `E`, by the hypothesis on
`X ∖ T`, and so does every infinitesimal neighbourhood of the reduced closed subscheme
supported on `W₀`, by the hypothesis on the completion. A monomorphism with a section is an
isomorphism, so the base change of `E ⟶ V` to each of those is an isomorphism, hence étale;
**Stacks 0A43** then makes `E ⟶ V` étale at every point over `W₀`, and over the open complement
it is an isomorphism. An étale monomorphism is an open immersion, and the same two
factorizations make it surjective, so `E ⟶ V` is an isomorphism and the two composites agree.

*Injectivity into the product.* The comparison map of Stacks 0GI3 goes into the fibre product
of `Mor(X', W)` and `Mor(X_{/T}, W)` over `Mor(X'_{/T}, W)`. That fibre product is a subtype of
the product, and `AlgebraicGeometry.Space.morToModificationCompletion_compatible` exhibits the
factorization through it, so injectivity of the comparison map is exactly injectivity of the
map into the product proved here.

## References

* [Stacks Project, Tag 0GI3](https://stacks.math.columbia.edu/tag/0GI3)
* [Stacks Project, Tag 0GI1](https://stacks.math.columbia.edu/tag/0GI1)
* [Stacks Project, Tag 0A43](https://stacks.math.columbia.edu/tag/0A43)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-! ### Morphisms out of a completion -/

/-- Two morphisms whose restrictions to the completion along `T` agree agree on every morphism
from a representable presheaf whose point-set image lies in `T`. -/
private theorem comp_eq_of_range_subset'
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a b : X ⟶ Y)
    {T : Set (points B S hS X)}
    (h : (completionSubfunctor B S hS X T).ι ≫ Functor.whiskerRight a uliftFunctor.{u + 1} =
      (completionSubfunctor B S hS X T).ι ≫ Functor.whiskerRight b uliftFunctor.{u + 1})
    {W : BigFppfOver B S hS} (q : yoneda.obj W ⟶ X)
    (hq : Set.range (pointsMap B S hS (yoneda.obj W) q) ⊆ T) :
    q ≫ a = q ≫ b := by
  have hx : HasImageIn B S hS X T W (yonedaEquiv q) := by
    rwa [hasImageIn_iff_range_subset, Equiv.symm_apply_apply]
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, yonedaEquiv_comp]
  exact congrArg ULift.down (congrFun (congrArg (fun α => α.app (op W)) h)
    (⟨ULift.up (yonedaEquiv q), hx⟩ : (completionSubfunctor B S hS X T).toFunctor.obj (op W)))

/-! ### Two morphisms agreeing off a closed subset and on its completion -/

/-- **The uniqueness statement of Stacks 0GI1.** Let `X` be a locally Noetherian algebraic space
over `S`, let `W` be an algebraic space over `S`, let `T ⊆ |X|` be a closed subset and let
`a, b : X ⟶ W` be morphisms. If `a` and `b` agree on the open subspace `X ∖ T` and the induced
morphisms `X_{/T} ⟶ W` agree, then `a = b`. -/
private theorem eq_of_eq_on_compl_of_eq_on_completion
    {X W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hW : IsAlgebraicSpace B S hS W)
    (hXnoeth : HasEtaleLocalProperty B S hS X (fun V : Scheme.{u} => IsLocallyNoetherian V))
    {T : Set (points B S hS X)} (hT : IsClosed T)
    (a b : X ⟶ W)
    (hcompl :
      (openSubspaceOfPoints B S hS X Tᶜ).ι ≫ a = (openSubspaceOfPoints B S hS X Tᶜ).ι ≫ b)
    (hcompletion :
      (completionSubfunctor B S hS X T).ι ≫ Functor.whiskerRight a uliftFunctor.{u + 1} =
        (completionSubfunctor B S hS X T).ι ≫ Functor.whiskerRight b uliftFunctor.{u + 1}) :
    a = b := by
  obtain ⟨V, p, hsurj, hetale, hVnoeth⟩ := hXnoeth
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) := hVnoeth
  refine hom_ext_of_etale_atlas B S hS hX.isSheaf hW.isSheaf p hsurj hetale ?_
  -- the inverse image of `T` in the atlas
  obtain ⟨Ws, hWsmem, hWsclosed⟩ :
      ∃ Ws : Set ((BigFppfOver.toScheme B S hS).obj V),
        (∀ w : points B S hS (yoneda.obj V),
          (pointsToScheme B S hS V w ∈ Ws ↔
            pointsMap B S hS (yoneda.obj V) p w ∈ T)) ∧ IsClosed Ws :=
    ⟨pointsToScheme B S hS V '' (pointsMap B S hS (yoneda.obj V) p ⁻¹' T),
      fun _ => (injective_pointsToScheme B S hS V).mem_set_image,
      (isClosed_pointTopology_yoneda_iff_isClosed_image B S hS V _).mp
        (hT.preimage (continuous_pointsMap B S hS p))⟩
  -- the point-set image of a site object mapping to the atlas
  have hrange : ∀ (Zo : BigFppfOver B S hS) (z : Zo ⟶ V)
      (w : points B S hS (yoneda.obj Zo)),
      pointsToScheme B S hS V (pointsMap B S hS (yoneda.obj Zo) (yoneda.map z) w) ∈
        Set.range ((BigFppfOver.toScheme B S hS).map z).base :=
    fun Zo z w => ⟨pointsToScheme B S hS Zo w, (pointsToScheme_pointsMap_yoneda B S hS z w).symm⟩
  refine comp_eq_of_sections B S hS hW V (p ≫ a) (p ≫ b) Ws hWsclosed ?_ ?_
  · intro Zo z hz
    rw [← Category.assoc, ← Category.assoc]
    refine comp_eq_of_range_subset' B S hS a b hcompletion _ ?_
    rintro _ ⟨w, rfl⟩
    rw [pointsMap_comp, Function.comp_apply]
    exact (hWsmem _).mp (hz (hrange Zo z w))
  · intro Zo z hz
    rw [← Category.assoc, ← Category.assoc]
    refine comp_eq_of_range_subset_compl B S hS a b hcompl _ ?_
    rintro _ ⟨w, rfl⟩
    rw [pointsMap_comp, Function.comp_apply]
    exact fun hmemT => hz (hrange Zo z w) ((hWsmem _).mpr hmemT)

/-! ### Stacks 0GI3 -/

/-- The comparison map of Stacks 0GI3: a morphism `w : X ⟶ W` is sent to its restriction
`X' ⟶ W` along `f : X' ⟶ X` together with the morphism `X_{/T} ⟶ W` it induces on the
completion of `X` along `T`. -/
def morToModificationCompletion {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X)
    (T : Set (points B S hS X)) (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (w : X ⟶ W) :
    (X' ⟶ W) × ((completionSubfunctor B S hS X T).toFunctor ⟶ W ⋙ uliftFunctor.{u + 1}) :=
  (f ≫ w,
    (completionSubfunctor B S hS X T).ι ≫ Functor.whiskerRight w uliftFunctor.{u + 1})

/-- The comparison map of Stacks 0GI3 lands in the fibre product: the restriction of `w` to `X'`
and the morphism it induces on `X_{/T}` induce the same morphism `X'_{/|f|⁻¹ T} ⟶ W`. -/
theorem morToModificationCompletion_compatible
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X)
    (T : Set (points B S hS X)) (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (w : X ⟶ W) :
    completionMap B S hS f T ≫ (morToModificationCompletion B S hS f T W w).2 =
      (completionSubfunctor B S hS X' (pointsMap B S hS X' f ⁻¹' T)).ι ≫
        Functor.whiskerRight (morToModificationCompletion B S hS f T W w).1
          uliftFunctor.{u + 1} := by
  ext U x
  rfl

/-- **Stacks 0GI3**, injectivity. Let `X` be a locally Noetherian algebraic space over `S`, let
`T ⊆ |X|` be a closed subset with complementary open subspace `U ⊆ X`, and let `f : X' ⟶ X` be a
proper morphism of algebraic spaces whose base change `f⁻¹(U) ⟶ U` is an isomorphism. For every
algebraic space `W` over `S` a morphism `X ⟶ W` is determined by its restriction to `X'`
together with the morphism `X_{/T} ⟶ W` it induces. -/
@[stacks 0GI3 "injectivity of the comparison map"]
theorem morToModificationCompletion_injective
    {X' X W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (_hX' : IsAlgebraicSpace B S hS X')
    (hW : IsAlgebraicSpace B S hS W)
    (hXnoeth : HasEtaleLocalProperty B S hS X (fun V : Scheme.{u} => IsLocallyNoetherian V))
    {T : Set (points B S hS X)} (hT : IsClosed T)
    (f : X' ⟶ X) (_hfproper : IsProper B S hS f)
    (hfU : IsIso (pullback.snd f (openSubspaceOfPoints B S hS X Tᶜ).ι)) :
    Function.Injective (morToModificationCompletion B S hS f T W) := by
  intro a b hab
  have h1 : f ≫ a = f ≫ b := congrArg Prod.fst hab
  refine eq_of_eq_on_compl_of_eq_on_completion B S hS hX hW hXnoeth hT a b ?_
    (congrArg Prod.snd hab)
  refine (cancel_epi (pullback.snd f (openSubspaceOfPoints B S hS X Tᶜ).ι)).mp ?_
  rw [← pullback.condition_assoc, ← pullback.condition_assoc, h1]

end Space

end AlgebraicGeometry

end
