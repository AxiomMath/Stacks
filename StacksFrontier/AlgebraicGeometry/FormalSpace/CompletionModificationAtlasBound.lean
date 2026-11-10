module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionCompletion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MorphismUniquenessAlongClosedSubset
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationAtlasSizeBound
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsInducingTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationSizeBounds
import all StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionDiagonal

/-!
# The uniform atlas bound of Stacks 0ARB

Let `X` be an algebraic space over `S`, let `T` be a set of points of `X`, and let
`g : W ⟶ X_{/T}` be a morphism of fppf sheaves from a sheaf `W` satisfying the set-theoretic
condition of Stacks 0AIS. In the proof of Stacks 0ARB, `W` is the given locally Noetherian formal
algebraic space, and the affine case Stacks 0ARA is applied over each member `h_R ⟶ X` of an
étale covering of `X` by affines. It produces a morphism `Z ⟶ h_R` locally of finite type, an
isomorphism over the complement of `T`, whose completion is the base change
`W_R = W ×_{X_{/T}} R_{/T}`. The descent datum formed by these `Z` is effective by Stacks 0ADV.

Effectivity along a covering of arbitrary size needs the spaces being descended to have atlases
of uniformly bounded size (`AlgebraicGeometry.Space.Descent.DescentData.isEffective_of_size_le`);
without a bound it fails. This file proves that bound: there is one cardinal `μ` below the
cutoff, depending only on `W`, `X` and a bound `κ` for the sizes of the members of the
covering, such that every such `Z` has an étale atlas of size at most `μ`.

The bound comes from `W`. The set-theoretic condition gives an object `U₀` of the site with a
surjection `h_{U₀} ⟶ W`. Its composite with `g` is the completion of a morphism
`x₀ : h_{U₀} ⟶ X` with image in `T`. Completion commutes with fibre products
(`AlgebraicGeometry.Space.isPullback_completionSheafMap_of_isPullback`), so the base change of
`h_{U₀} ⟶ W` to `W_R` is the completion of `Q = R ×_X U₀` along all of `|Q|`, which is `h_Q`.
So `h_Q` surjects onto `W_R ≅ Z_{/T}`. The size of `Q` is bounded in terms of `size R` and
`size U₀` alone, because `Q ⟶ R ×_S U₀` is a monomorphism. Then
`AlgebraicGeometry.Space.exists_atlas_size_le_of_epi_completionSheaf` bounds the atlas of `Z`.

## Main results

* `AlgebraicGeometry.Space.exists_eq_completionSheafMap`: a morphism from a representable sheaf
  into `X_{/T}` is the completion of a morphism into `X` with image in `T`.
* `AlgebraicGeometry.Space.exists_epi_uliftYoneda_pullback_completionSheafMap`: the base change
  of `W` to `R_{/T}` receives a surjection from a representable sheaf of controlled size.
* `AlgebraicGeometry.Space.exists_uniform_atlas_size_bound`: the uniform atlas bound.

## References

* [Stacks Project, Tag 0ARB](https://stacks.math.columbia.edu/tag/0ARB)
* [Stacks Project, Tag 0ADV](https://stacks.math.columbia.edu/tag/0ADV)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0APV](https://stacks.math.columbia.edu/tag/0APV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u v

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The identification of the completion of a sheaf with the subfunctor of sections with
image in the set of points is natural in the sheaf. -/
theorem completionSheafMap_hom_comp_completionSheafIsoSubfunctor_hom
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X')
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X) (f : X' ⟶ X)
    (T : Set (points B S hS X)) :
    (completionSheafMap B S hS f T).hom ≫ (completionSheafIsoSubfunctor B S hS hX T).hom =
      (completionSheafIsoSubfunctor B S hS hX' _).hom ≫ completionMap B S hS f T := by
  change (BigFppfOver.topology B S hS).sheafifyMap (completionMap B S hS f T) ≫
      ((BigFppfOver.topology B S hS).isoSheafify
        (isSheaf_completionSubfunctor B S hS hX T)).inv =
    ((BigFppfOver.topology B S hS).isoSheafify
        (isSheaf_completionSubfunctor B S hS hX' _)).inv ≫ completionMap B S hS f T
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp,
    GrothendieckTopology.isoSheafify_hom, GrothendieckTopology.isoSheafify_hom]
  exact (GrothendieckTopology.toSheafify_naturality _ _).symm

/-- The sections of the universe-lifted representable presheaf of `V` are the sections of the
completion subfunctor of `h_V` along all of its points. -/
def uliftYonedaIsoCompletionSubfunctor (V : BigFppfOver B S hS)
    {Z : Set (points B S hS (yoneda.obj V))} (hZ : Z = Set.univ) :
    uliftYoneda.{u + 1}.obj V ≅ (completionSubfunctor B S hS (yoneda.obj V) Z).toFunctor :=
  NatIso.ofComponents (fun U => Equiv.toIso
    { toFun := fun v => ⟨v, by subst hZ; exact hasImageIn_univ B S hS _ U.unop v.down⟩
      invFun := fun s => s.1
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }) (by intros; rfl)

/-- **`V_{/V} = V`.** The universe-lifted representable sheaf of `V` is the completion of `h_V`
along all of its points. -/
def uliftYonedaIsoCompletionSheaf (V : BigFppfOver B S hS)
    {Z : Set (points B S hS (yoneda.obj V))} (hZ : Z = Set.univ) :
    (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj V ≅
      completionSheaf B S hS (yoneda.obj V) Z :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    ((BigFppfOver.topology B S hS).uliftYonedaCompSheafToPresheaf.app V ≪≫
      uliftYonedaIsoCompletionSubfunctor V hZ ≪≫
      (completionSheafIsoSubfunctor B S hS (isAlgebraicSpace_yoneda B S hS V).isSheaf Z).symm)

/-- The presheaf component of `uliftYonedaIsoCompletionSheaf`, followed by the identification of
the completion sheaf with the completion subfunctor, is the identification of the lifted
representable sheaf with the lifted representable presheaf followed by
`uliftYonedaIsoCompletionSubfunctor`. -/
theorem uliftYonedaIsoCompletionSheaf_hom_hom_comp (V : BigFppfOver B S hS)
    {Z : Set (points B S hS (yoneda.obj V))} (hZ : Z = Set.univ) :
    (uliftYonedaIsoCompletionSheaf V hZ).hom.hom ≫
        (completionSheafIsoSubfunctor B S hS (isAlgebraicSpace_yoneda B S hS V).isSheaf Z).hom =
      ((BigFppfOver.topology B S hS).uliftYonedaCompSheafToPresheaf.app V).hom ≫
        (uliftYonedaIsoCompletionSubfunctor V hZ).hom := by
  have h : (uliftYonedaIsoCompletionSheaf V hZ).hom.hom =
      ((BigFppfOver.topology B S hS).uliftYonedaCompSheafToPresheaf.app V ≪≫
        uliftYonedaIsoCompletionSubfunctor V hZ ≪≫
        (completionSheafIsoSubfunctor B S hS (isAlgebraicSpace_yoneda B S hS V).isSheaf
          Z).symm).hom :=
    (fullyFaithfulSheafToPresheaf _ _).map_preimage _
  rw [h]
  simp

/-- **A morphism from a representable sheaf into a completion is a completed morphism.** Let `X`
be an fppf sheaf, `T` a set of its points and `h₀ : h_{U₀} ⟶ X_{/T}` a morphism from the
universe-lifted representable sheaf of an object `U₀`. Then `h₀` is the completion of a morphism
`x₀ : h_{U₀} ⟶ X` whose point-set image lies in `T`, read through `V_{/V} = V`. -/
theorem exists_eq_completionSheafMap {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X) (T : Set (points B S hS X))
    {U₀ : BigFppfOver B S hS}
    (h₀ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U₀ ⟶ completionSheaf B S hS X T) :
    ∃ (x₀ : yoneda.obj U₀ ⟶ X) (hZ : pointsMap B S hS _ x₀ ⁻¹' T = Set.univ),
      (uliftYonedaIsoCompletionSheaf U₀ hZ).hom ≫ completionSheafMap B S hS x₀ T = h₀ := by
  let J := BigFppfOver.topology B S hS
  let eP := J.uliftYonedaCompSheafToPresheaf.app U₀
  let κ₀ := eP.inv ≫ h₀.hom ≫ (completionSheafIsoSubfunctor B S hS hX T).hom
  let s₀ := κ₀.app (op U₀) (ULift.up (𝟙 U₀))
  let x₀ : yoneda.obj U₀ ⟶ X := yonedaEquiv.symm s₀.1.down
  have hZ : pointsMap B S hS _ x₀ ⁻¹' T = Set.univ :=
    Set.eq_univ_of_forall fun z =>
      (hasImageIn_iff_range_subset B S hS T U₀ s₀.1.down).1 s₀.2 ⟨z, rfl⟩
  refine ⟨x₀, hZ, ?_⟩
  apply ObjectProperty.hom_ext
  rw [← cancel_mono (completionSheafIsoSubfunctor B S hS hX T).hom, ← cancel_epi eP.inv,
    ObjectProperty.FullSubcategory.comp_hom, Category.assoc,
    completionSheafMap_hom_comp_completionSheafIsoSubfunctor_hom
      (isAlgebraicSpace_yoneda B S hS U₀).isSheaf hX,
    ← Category.assoc _ _ (completionMap _ _ _ _ _),
    uliftYonedaIsoCompletionSheaf_hom_hom_comp, ← Category.assoc, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]
  apply uliftYonedaEquiv.injective
  apply Subtype.ext
  apply ULift.ext
  change x₀.app (op U₀) (𝟙 U₀) = s₀.1.down
  exact X.map_id_apply _ s₀.1.down

/-- Iterating Cantor's inequality: a cardinal is at most `2 ^ 2 ^ a`. -/
private theorem le_two_pow_two_pow (a : Cardinal.{u}) :
    a ≤ (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ a :=
  (cantor a).le.trans (cantor _).le

/-- **The size of a fibre product over an algebraic space.** If `h_Q` is the fibre product of
`h_R ⟶ X` and `h_{U₀} ⟶ X` over an algebraic space `X`, then `size Q ≤ 2 ^ 2 ^ m` where `m` is
the larger of `size R` and `size U₀`. The morphism `Q ⟶ R ×_S U₀` is a monomorphism, so Stacks
04T6 and the bound for the source of a monomorphism apply. -/
theorem size_le_of_isPullback_yoneda {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {R U₀ Q : BigFppfOver B S hS} {e : yoneda.obj R ⟶ X} {x₀ : yoneda.obj U₀ ⟶ X}
    {fst : yoneda.obj Q ⟶ yoneda.obj R} {snd : Q ⟶ U₀}
    (h : IsPullback fst (yoneda.map snd) e x₀) :
    ((BigFppfOver.toScheme B S hS).obj Q).size ≤
      (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ max ((BigFppfOver.toScheme B S hS).obj R).size
        ((BigFppfOver.toScheme B S hS).obj U₀).size := by
  let A := BigFppfOver.toScheme B S hS
  let top : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))
  let tR : R ⟶ top := Over.homMk R.hom
  let tU : U₀ ⟶ top := Over.homMk U₀.hom
  have htop : ∀ {Y : BigFppfOver B S hS} (a b : Y ⟶ top), a = b := fun {Y} a b =>
    Over.OverMorphism.ext (by
      have ha : a.left ≫ 𝟙 (B.obj hS) = Y.hom := Over.w a
      have hb : b.left ≫ 𝟙 (B.obj hS) = Y.hom := Over.w b
      exact (Category.comp_id _).symm.trans (ha.trans (hb.symm.trans (Category.comp_id _))))
  let m : Q ⟶ pullback tR tU := pullback.lift (yoneda.preimage fst) snd (htop _ _)
  have hm : Mono m := ⟨fun a b hab => by
    apply yoneda.map_injective
    have h₁ : a ≫ yoneda.preimage fst = b ≫ yoneda.preimage fst := by
      simpa only [Category.assoc, m, pullback.lift_fst] using congrArg (· ≫ pullback.fst tR tU) hab
    have h₂ : a ≫ snd = b ≫ snd := by
      simpa only [Category.assoc, m, pullback.lift_snd] using congrArg (· ≫ pullback.snd tR tU) hab
    refine h.hom_ext ?_ ?_
    · rw [← yoneda.map_preimage fst, ← Functor.map_comp, ← Functor.map_comp, h₁]
    · rw [← Functor.map_comp, ← Functor.map_comp, h₂]⟩
  have h₁ : (A.obj Q).size ≤ max (2 ^ #(A.obj (pullback tR tU))) (A.obj (pullback tR tU)).size :=
    have := mono_toScheme_map B S hS m
    Scheme.size_le_of_mono (A.map m)
  have h₂ : (A.obj (pullback tR tU)).size ≤ max (A.obj R).size (A.obj U₀).size :=
    size_pullback_le B S hS tR tU
  refine h₁.trans (max_le ?_ ?_)
  · exact power_le_power_left two_ne_zero
      ((Scheme.mk_le_two_pow_size (A.obj (pullback tR tU))).trans
        (power_le_power_left two_ne_zero h₂))
  · exact h₂.trans (le_two_pow_two_pow _)

/-- **The base change of a sheaf covered by a representable to the completion of a chart is
covered by a representable of controlled size.**

Let `X` be an algebraic space, `T` a set of its points, `g : W ⟶ X_{/T}` a morphism of fppf
sheaves and `f₀ : h_{U₀} ⟶ W` a surjection from a representable sheaf. For every morphism
`e : h_R ⟶ X` from a representable presheaf, the base change `W ×_{X_{/T}} R_{/T}` receives a
surjection from the representable sheaf of an object `Q` with
`size Q ≤ 2 ^ 2 ^ max (size R) (size U₀)`.

The composite `f₀ ≫ g` is the completion of some `x₀ : h_{U₀} ⟶ X`
(`AlgebraicGeometry.Space.exists_eq_completionSheafMap`), and `Q = R ×_X U₀`. Completion
preserves the fibre product (Stacks 0APV, in the form
`AlgebraicGeometry.Space.isPullback_completionSheafMap_of_isPullback`) and the completions of
`U₀` and `Q` are along all of their points, so `h_Q ⟶ W ×_{X_{/T}} R_{/T}` is the base change of
`f₀`, hence surjective. -/
theorem exists_epi_uliftYoneda_pullback_completionSheafMap {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (T : Set (points B S hS X)) {U₀ : BigFppfOver B S hS}
    {W : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    (f₀ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U₀ ⟶ W) [Epi f₀]
    (g : W ⟶ completionSheaf B S hS X T) {R : BigFppfOver B S hS} (e : yoneda.obj R ⟶ X) :
    ∃ (Q : BigFppfOver B S hS)
      (q : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj Q ⟶
        pullback g (completionSheafMap B S hS e T)),
      Epi q ∧ ((BigFppfOver.toScheme B S hS).obj Q).size ≤
        (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ max ((BigFppfOver.toScheme B S hS).obj R).size
          ((BigFppfOver.toScheme B S hS).obj U₀).size := by
  let J := BigFppfOver.topology B S hS
  obtain ⟨x₀, hZ, hx₀⟩ := exists_eq_completionSheafMap hX.isSheaf T (f₀ ≫ g)
  have hrep : yoneda.relativelyRepresentable e :=
    Functor.relativelyRepresentable.of_diag hX.diagonal_representable e
  let Q := hrep.pullback x₀
  let fstQ : yoneda.obj Q ⟶ yoneda.obj R := yoneda.map (hrep.fst' x₀)
  let sndQ : Q ⟶ U₀ := hrep.snd x₀
  have hpb : IsPullback fstQ (yoneda.map sndQ) e x₀ := hrep.isPullback' x₀
  have hc := isPullback_completionSheafMap_of_isPullback B S hS hpb T
  have hZQ : pointsMap B S hS _ fstQ ⁻¹' (pointsMap B S hS _ e ⁻¹' T) = Set.univ := by
    rw [preimage_pointsMap_eq_of_comm B S hS hpb.w T, hZ, Set.preimage_univ]
  let isoU := uliftYonedaIsoCompletionSheaf U₀ hZ
  let isoQ := uliftYonedaIsoCompletionSheaf Q hZQ
  let a' := (eqToHom (congrArg (completionSheaf B S hS (yoneda.obj Q))
      (preimage_pointsMap_eq_of_comm B S hS hpb.w T)) ≫
    completionSheafMap B S hS (yoneda.map sndQ) (pointsMap B S hS _ x₀ ⁻¹' T)) ≫ isoU.inv
  have big : IsPullback a' (completionSheafMap B S hS fstQ (pointsMap B S hS _ e ⁻¹' T))
      (f₀ ≫ g) (completionSheafMap B S hS e T) :=
    hc.flip.of_iso (Iso.refl _) isoU.symm (Iso.refl _) (Iso.refl _) (by simp [a'])
      (by simp) (by rw [← hx₀]; simp) (by simp)
  let lift : completionSheaf B S hS (yoneda.obj Q)
      (pointsMap B S hS _ fstQ ⁻¹' (pointsMap B S hS _ e ⁻¹' T)) ⟶
      pullback g (completionSheafMap B S hS e T) :=
    pullback.lift (a' ≫ f₀) (completionSheafMap B S hS fstQ _) ((Category.assoc _ _ _).trans big.w)
  have small : IsPullback a' lift f₀ (pullback.fst g (completionSheafMap B S hS e T)) :=
    IsPullback.of_bot (by rwa [pullback.lift_snd]) (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback _ _)
  have : Presheaf.IsLocallySurjective J ((sheafToPresheaf J _).map f₀) :=
    (Sheaf.isLocallySurjective_iff_epi f₀).2 inferInstance
  have hlift : Presheaf.IsLocallySurjective J lift.hom :=
    Presheaf.isLocallySurjective_of_isPullback J (small.flip.map (sheafToPresheaf J _))
  have : Epi lift := (Sheaf.isLocallySurjective_iff_epi lift).1 hlift
  exact ⟨Q, isoQ.hom ≫ lift, inferInstance, size_le_of_isPullback_yoneda hpb⟩

/-- **The uniform atlas bound of Stacks 0ARB.**

Let `X` be an algebraic space over `S`, `T` a set of points of `X`, and `g : W ⟶ X_{/T}` a
morphism of fppf sheaves whose source satisfies the set-theoretic condition of Stacks 0AIS. This
holds for every formal algebraic space `W`, by Definition 0AIM. Let `κ` be a cardinal below the
cutoff. Then there is a cardinal `μ` with `ℵ₀ ≤ μ < B.cutoff` such that the following holds.
Let `e : h_R ⟶ X` be a morphism from an object of the site with `size R ≤ κ`, and let
`p : Z ⟶ h_R` be a morphism of algebraic spaces, locally of finite type, which is an
isomorphism over the complement `U_R` of `T_R = |e|⁻¹T`. Suppose the completion of `Z` along
`|p|⁻¹T_R` is isomorphic to `W ×_{X_{/T}} R_{/T}`. Then `Z` has a surjective étale atlas of size
at most `μ`.

In the proof of Stacks 0ARB, the `Z` are the outputs of Stacks 0ARA over the members of an
étale covering of `X` by affines of size at most `κ`. This is the bound which
`AlgebraicGeometry.Space.Descent.DescentData.isEffective_of_size_le` needs to make the descent
datum they form effective. Effectivity fails without such a bound.

The proof takes a surjection `h_{U₀} ⟶ W` from the set-theoretic condition. Over each `R`,
`AlgebraicGeometry.Space.exists_epi_uliftYoneda_pullback_completionSheafMap` gives a surjection
from `h_Q` onto the completion of `Z` with `size Q` bounded in terms of `size R` and `size U₀`
only. `AlgebraicGeometry.Space.exists_atlas_size_le_of_epi_completionSheaf` then gives the
atlas. The cardinal is `μ = 2 ^ 2 ^ 2 ^ max κ (size U₀)`. -/
theorem exists_uniform_atlas_size_bound {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (T : Set (points B S hS X))
    {W : FormalSpace.FppfSheaf B S hS} (hW : FormalSpace.SatisfiesSetTheoreticCondition B S hS W)
    (g : W ⟶ completionSheaf B S hS X T) {κ : Cardinal.{u}} (hκ : κ < B.cutoff) :
    ∃ μ : Cardinal.{u}, ℵ₀ ≤ μ ∧ μ < B.cutoff ∧
      ∀ (R : BigFppfOver B S hS) (e : yoneda.obj R ⟶ X),
        ((BigFppfOver.toScheme B S hS).obj R).size ≤ κ →
        ∀ {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : Z ⟶ yoneda.obj R),
          IsAlgebraicSpace B S hS Z → IsLocallyOfFiniteType B S hS p →
          IsIso (pullback.snd p
            (openSubspaceOfPoints B S hS (yoneda.obj R) (pointsMap B S hS _ e ⁻¹' T)ᶜ).ι) →
          (completionSheaf B S hS Z (pointsMap B S hS Z p ⁻¹' (pointsMap B S hS _ e ⁻¹' T)) ≅
            pullback g (completionSheafMap B S hS e T)) →
          ∃ (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ Z),
            (MorphismProperty.presheaf (MorphismProperty.inverseImage
              (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
            (MorphismProperty.presheaf (MorphismProperty.inverseImage
              (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
            ((BigFppfOver.toScheme B S hS).obj V).size ≤ μ := by
  let J := BigFppfOver.topology B S hS
  obtain ⟨U₀, -, hU, -, ⟨eU⟩, -, f, hf, -⟩ := hW
  let f₀ : J.uliftYoneda.{u + 1}.obj U₀ ⟶ W :=
    ((fullyFaithfulSheafToPresheaf J _).preimageIso
      (J.uliftYonedaCompSheafToPresheaf.app U₀ ≪≫ eU.symm)).hom ≫ f
  have : Epi f₀ := inferInstance
  set κ' := max κ ((BigFppfOver.toScheme B S hS).obj U₀).size
  have hκ' : κ' < B.cutoff := max_lt hκ U₀.left.property
  have hpow : ∀ {a b : Cardinal.{u}}, a ≤ b → (2 : Cardinal.{u}) ^ a ≤ 2 ^ b :=
    fun h => power_le_power_left two_ne_zero h
  have hκμ : κ' ≤ (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ κ' :=
    (le_two_pow_two_pow _).trans (cantor _).le
  have hμℵ : ℵ₀ ≤ (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ κ' :=
    ((Scheme.aleph0_le_size _).trans (le_max_right _ _)).trans hκμ
  have hμ : (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ κ' < B.cutoff :=
    B.cutoff_isStrongPrelimit (B.cutoff_isStrongPrelimit (B.cutoff_isStrongPrelimit hκ'))
  refine ⟨_, hμℵ, hμ, ?_⟩
  intro R e hRκ Z p hZ hp hiso β
  obtain ⟨Q, q, hq, hQ⟩ := exists_epi_uliftYoneda_pullback_completionSheafMap hX T f₀ g e
  have := hq
  have : Epi (q ≫ β.inv) := inferInstance
  have hRκ' : ((BigFppfOver.toScheme B S hS).obj R).size ≤ κ' := hRκ.trans (le_max_left _ _)
  refine exists_atlas_size_le_of_epi_completionSheaf hZ p hp _ hiso (q ≫ β.inv) hμℵ hμ
    (hRκ'.trans hκμ) ?_ ?_
  · exact (Scheme.mk_le_two_pow_size _).trans
      ((hpow hRκ').trans (le_two_pow_two_pow _))
  · exact (Scheme.mk_le_two_pow_size _).trans
      (hpow (hQ.trans (hpow (hpow (max_le hRκ' (le_max_right _ _))))))

/-- The inverse image of a set of points under a composite. -/
theorem preimage_pointsMap_preimage_pointsMap {Y₁ Y₂ Y₃ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : Y₁ ⟶ Y₂) (b : Y₂ ⟶ Y₃) (T : Set (points B S hS Y₃)) :
    pointsMap B S hS _ a ⁻¹' (pointsMap B S hS _ b ⁻¹' T) = pointsMap B S hS _ (a ≫ b) ⁻¹' T := by
  rw [pointsMap_comp, Set.preimage_comp]

/-- Completion along `T` of a composite is the composite of the completions, up to the
identification of the inverse image of `T` under the composite. -/
theorem completionSheafMap_comp_completionSheafMap {Y₁ Y₂ Y₃ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : Y₁ ⟶ Y₂) (b : Y₂ ⟶ Y₃) (T : Set (points B S hS Y₃)) :
    completionSheafMap B S hS a (pointsMap B S hS _ b ⁻¹' T) ≫ completionSheafMap B S hS b T =
      eqToHom (congrArg (completionSheaf B S hS Y₁) (preimage_pointsMap_preimage_pointsMap a b T)) ≫
        completionSheafMap B S hS (a ≫ b) T := by
  have := mono_completionSheafInclusion B S hS Y₃ T
  rw [← cancel_mono (completionSheafInclusion B S hS Y₃ T), Category.assoc, Category.assoc,
    ← (isPullback_completionSheafMap B S hS b T).w,
    ← (isPullback_completionSheafMap B S hS (a ≫ b) T).w, ← Category.assoc,
    ← (isPullback_completionSheafMap B S hS a _).w, Category.assoc, ← sheafifiedULiftMap_comp,
    ← Category.assoc, eqToHom_comp_completionSheafInclusion B S hS Y₁
      (preimage_pointsMap_preimage_pointsMap a b T)]

/-- **The completion of a base change of a member of the descent datum.** Let `q : Y ⟶ Xᵢ` have
completion along the inverse image of `T` identified with `W ×_{X_{/T}} (Xᵢ)_{/T}` over
`(Xᵢ)_{/T}`, where `eᵢ : Xᵢ ⟶ X`. For `b : V ⟶ Xᵢ` the completion of `Y ×_{Xᵢ} V` along the
inverse image of `T` is then `W ×_{X_{/T}} V_{/T}`, the completion being taken along
`b ≫ eᵢ`. -/
theorem nonempty_completionSheaf_pullback_iso {X Y Xᵢ V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (points B S hS X)) {W : FormalSpace.FppfSheaf B S hS}
    (g : W ⟶ completionSheaf B S hS X T) (q : Y ⟶ Xᵢ) (eᵢ : Xᵢ ⟶ X)
    (β : completionSheaf B S hS Y (pointsMap B S hS _ q ⁻¹' (pointsMap B S hS _ eᵢ ⁻¹' T)) ≅
      pullback g (completionSheafMap B S hS eᵢ T))
    (hβ : β.hom ≫ pullback.snd _ _ = completionSheafMap B S hS q _) (b : V ⟶ Xᵢ) :
    Nonempty (completionSheaf B S hS (pullback q b)
        (pointsMap B S hS _ (pullback.snd q b) ⁻¹' (pointsMap B S hS _ (b ≫ eᵢ) ⁻¹' T)) ≅
      pullback g (completionSheafMap B S hS (b ≫ eᵢ) T)) := by
  have H₁ := isPullback_completionSheafMap_of_isPullback B S hS
    (IsPullback.of_hasPullback q b) (pointsMap B S hS _ eᵢ ⁻¹' T)
  have H₂ : IsPullback (β.hom ≫ pullback.fst g (completionSheafMap B S hS eᵢ T))
      (completionSheafMap B S hS q _) g (completionSheafMap B S hS eᵢ T) :=
    (IsPullback.of_hasPullback g (completionSheafMap B S hS eᵢ T)).of_iso β.symm (Iso.refl _)
      (Iso.refl _) (Iso.refl _) (by simp) (by simp [← hβ]) (by simp) (by simp)
  have hV := preimage_pointsMap_preimage_pointsMap b eᵢ T
  have hset : pointsMap B S hS _ (pullback.snd q b) ⁻¹' (pointsMap B S hS _ (b ≫ eᵢ) ⁻¹' T) =
      pointsMap B S hS _ (pullback.fst q b) ⁻¹'
        (pointsMap B S hS _ q ⁻¹' (pointsMap B S hS _ eᵢ ⁻¹' T)) := by
    rw [preimage_pointsMap_eq_of_comm B S hS pullback.condition, ← hV]
  have H' := (H₁.paste_horiz H₂).of_iso (Iso.refl _) (Iso.refl _)
    (eqToIso (congrArg (completionSheaf B S hS V) hV)) (Iso.refl _)
    (fst' := completionSheafMap B S hS (pullback.fst q b) _ ≫ β.hom ≫ pullback.fst _ _)
    (snd' := (eqToHom (congrArg (completionSheaf B S hS (pullback q b))
        (preimage_pointsMap_eq_of_comm B S hS pullback.condition
          (pointsMap B S hS _ eᵢ ⁻¹' T))) ≫
        completionSheafMap B S hS (pullback.snd q b) _) ≫
      eqToHom (congrArg (completionSheaf B S hS V) hV))
    (f' := g) (g' := completionSheafMap B S hS (b ≫ eᵢ) T)
    (by simp) (by simp) (by simp)
    (by rw [completionSheafMap_comp_completionSheafMap]; simp)
  exact ⟨eqToIso (congrArg (completionSheaf B S hS (pullback q b)) hset) ≪≫ H'.isoPullback⟩

namespace Descent.DescentData

/-- `Z` has a surjective étale atlas of size at most `μ`. -/
private def HasAtlasOfSizeLE (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (μ : Cardinal.{u}) : Prop :=
  ∃ (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ Z),
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
    ((BigFppfOver.toScheme B S hS).obj V).size ≤ μ

private theorem HasAtlasOfSizeLE.mono {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {μ ν : Cardinal.{u}} (h : HasAtlasOfSizeLE Z μ) (hμν : μ ≤ ν) : HasAtlasOfSizeLE Z ν :=
  have ⟨V, a, hs, he, hV⟩ := h
  ⟨V, a, hs, he, hV.trans hμν⟩

/-- A representable presheaf has an atlas by itself. -/
private theorem hasAtlasOfSizeLE_yoneda (R : BigFppfOver B S hS) {μ : Cardinal.{u}}
    (hR : ((BigFppfOver.toScheme B S hS).obj R).size ≤ μ) :
    HasAtlasOfSizeLE (yoneda.obj R) μ :=
  ⟨R, 𝟙 _, presheaf_surjective_id B S hS R, presheaf_etale_id B S hS R, hR⟩

/-- **The descent datum of Stacks 0ARB is effective.**

Let `{e i : h_{R i} ⟶ X}` be an fppf covering of an algebraic space `X` by representable
presheaves, with the index type and every `size (R i)` bounded by one cardinal `κ` below the
cutoff. Let `T` be a set of points of `X` and `g : W ⟶ X_{/T}` a morphism from a sheaf satisfying
the set-theoretic condition of Stacks 0AIS. Let `(Y i, φ i j)` be a descent datum relative to the
covering such that each `Y i ⟶ h_{R i}` is locally of finite type, is an isomorphism over the
complement of `T_i = |e i|⁻¹T`, and has completion along the inverse image of `T_i` isomorphic to
`W ×_{X_{/T}} (R i)_{/T}`. Then the descent datum is effective.

This is the source's appeal to Stacks 0ADV in the proof of Stacks 0ARB. The members of the datum
are only locally of finite type over the `R i`, so neither part of 0ADV applies as stated, and
for an index set of uncountable cofinality effectivity can fail. What makes it hold is the
uniform atlas bound `AlgebraicGeometry.Space.exists_uniform_atlas_size_bound`, which is derived
from `W`. `AlgebraicGeometry.Space.Descent.DescentData.isEffective_of_size_le` then applies. -/
theorem isEffective_of_completion_iso {ι : Type v} [Small.{u} ι] {R : ι → BigFppfOver B S hS}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {e : ∀ i, yoneda.obj (R i) ⟶ X}
    {hX : IsAlgebraicSpace B S hS X} {hR : ∀ i, IsAlgebraicSpace B S hS (yoneda.obj (R i))}
    (D : DescentData e hX hR) (hcov : IsFppfCovering B S hS (fun i ↦ yoneda.obj (R i)) e)
    (T : Set (points B S hS X)) {W : FormalSpace.FppfSheaf B S hS}
    (hW : FormalSpace.SatisfiesSetTheoreticCondition B S hS W)
    (g : W ⟶ completionSheaf B S hS X T) {κ : Cardinal.{u}} (hκ : κ < B.cutoff)
    (_ : ℵ₀ ≤ κ) (hι : #(Shrink.{u} ι) ≤ κ)
    (hRκ : ∀ i, ((BigFppfOver.toScheme B S hS).obj (R i)).size ≤ κ)
    (hft : ∀ i, IsLocallyOfFiniteType B S hS (D.obj i).hom)
    (hiso : ∀ i, IsIso (pullback.snd (D.obj i).hom
      (openSubspaceOfPoints B S hS (yoneda.obj (R i)) (pointsMap B S hS _ (e i) ⁻¹' T)ᶜ).ι))
    (hcompl : ∀ i, Nonempty (completionSheaf B S hS (D.obj i).left
        (pointsMap B S hS _ (D.obj i).hom ⁻¹' (pointsMap B S hS _ (e i) ⁻¹' T)) ≅
      pullback g (completionSheafMap B S hS (e i) T))) :
    D.IsEffective := by
  obtain ⟨μ, hμℵ, hμ, hbound⟩ := exists_uniform_atlas_size_bound hX T hW g hκ
  refine D.isEffective_of_size_le hcov (μ := max μ κ) (le_max_of_le_left hμℵ) (max_lt hμ hκ)
    (hι.trans (le_max_right _ _)) (fun i ↦ ?_) (fun i ↦ ?_)
  · exact hasAtlasOfSizeLE_yoneda (R i) ((hRκ i).trans (le_max_right _ _))
  · exact HasAtlasOfSizeLE.mono (hbound (R i) (e i) (hRκ i) (D.obj i).hom
      (D.obj_isAlgebraicSpace i) (hft i) (hiso i) (hcompl i).some) (le_max_left _ _)

/-- **The descent datum of Stacks 0ARB is effective, for an fppf covering of any size.**

Let `{e i : X i ⟶ X}` be an fppf covering of an algebraic space `X`, indexed by a type of any
size, let `T` be a set of points of `X`, and let `g : W ⟶ X_{/T}` be a morphism from a sheaf
satisfying the set-theoretic condition of Stacks 0AIS (for instance a formal algebraic space).
Let `(Y i, φ i j)` be a descent datum relative to the covering. Suppose each `Y i ⟶ X i` is
locally of finite type and an isomorphism over the complement of `T_i = |e i|⁻¹T`, and that its
completion along the inverse image of `T_i` is identified, over `(X i)_{/T}`, with
`W_i = W ×_{X_{/T}} (X i)_{/T}`. Then the descent datum is effective.

These are the hypotheses the proof of Stacks 0ARB has when it applies Stacks 0ADV to the outputs
`X'_i` of Stacks 0ARA. Neither part of 0ADV covers them, and for an index set of uncountable
cofinality effectivity of an étale descent datum whose pieces are only locally of finite type
can fail. The proof runs as for part (2) of 0ADV
(`AlgebraicGeometry.Space.Descent.DescentData.isEffective_of_isFiniteType`). Refine the covering
by a bounded fppf covering `{R k ⟶ X}` by affines. The fibres `R k ×_{X i} Y i` of the glued sheaf
are locally of finite type over `R k`, isomorphisms off `T`, and have completion
`W ×_{X_{/T}} (R k)_{/T}`
(`AlgebraicGeometry.Space.nonempty_completionSheaf_pullback_iso`). So the uniform atlas bound
`AlgebraicGeometry.Space.exists_uniform_atlas_size_bound` applies to them. Stacks 02WQ and
Stacks 04S6 then make the glued sheaf an algebraic space. -/
theorem isEffective_of_completionSheaf_iso {ι : Type v} {X : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {e : ∀ i, X i ⟶ Y₀}
    {hY₀ : IsAlgebraicSpace B S hS Y₀} {hX : ∀ i, IsAlgebraicSpace B S hS (X i)}
    (D : DescentData e hY₀ hX) (hcov : IsFppfCovering B S hS X e)
    (T : Set (points B S hS Y₀)) {W : FormalSpace.FppfSheaf B S hS}
    (hW : FormalSpace.SatisfiesSetTheoreticCondition B S hS W)
    (g : W ⟶ completionSheaf B S hS Y₀ T)
    (hft : ∀ i, IsLocallyOfFiniteType B S hS (D.obj i).hom)
    (hiso : ∀ i, IsIso (pullback.snd (D.obj i).hom
      (openSubspaceOfPoints B S hS (X i) (pointsMap B S hS _ (e i) ⁻¹' T)ᶜ).ι))
    (β : ∀ i, completionSheaf B S hS (D.obj i).left
        (pointsMap B S hS _ (D.obj i).hom ⁻¹' (pointsMap B S hS _ (e i) ⁻¹' T)) ≅
      pullback g (completionSheafMap B S hS (e i) T))
    (hβ : ∀ i, (β i).hom ≫ pullback.snd _ _ = completionSheafMap B S hS (D.obj i).hom _) :
    D.IsEffective := by
  obtain ⟨K, R, r, a, b, μ₀, hcovR, hbr, -, hℵ, hμ₀, hK, hsize⟩ :=
    exists_affine_refinement_of_isFppfCovering hcov
  obtain ⟨μ₁, hμ₁ℵ, hμ₁, hbound⟩ := exists_uniform_atlas_size_bound hY₀ T hW g hμ₀
  set μ := max μ₁ μ₀
  have hμℵ : ℵ₀ ≤ μ := le_max_of_le_left hμ₁ℵ
  have hμ : μ < B.cutoff := max_lt hμ₁ hμ₀
  have hKs : #(Shrink.{u} K) ≤ μ :=
    (Cardinal.mk_congr (equivShrink.{u} K)).symm.le.trans (hK.trans (le_max_right _ _))
  let Z : K → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u := fun k ↦ pullback (D.obj (a k)).hom (b k)
  have hZ : ∀ k, IsAlgebraicSpace B S hS (Z k) := fun k ↦
    isAlgebraicSpace_pullback B S hS _ _ (D.obj_isAlgebraicSpace (a k))
      (isAlgebraicSpace_yoneda B S hS (R k)) (hX (a k))
  have hpb : ∀ k, IsPullback
      (pullback.fst (D.obj (a k)).hom (b k) ≫ descentInclusion e hcov D (a k))
      (pullback.snd (D.obj (a k)).hom (b k))
      ((fppfDescentDataSheafEquivalence e hcov).inverse.obj D).obj.hom (r k) := fun k ↦ by
    rw [← hbr k]
    exact (IsPullback.of_hasPullback (D.obj (a k)).hom (b k)).paste_horiz
      (isPullback_descentInclusion e hcov D (a k))
  have hZat : ∀ k, HasAtlasOfSizeLE (Z k) μ := fun k ↦ by
    have hM := isFiniteTypeModification_pullback (isAlgebraicSpace_yoneda B S hS (R k))
      (hX (a k)) (b k) _ (M := D.obj (a k))
      ⟨⟨D.obj_isAlgebraicSpace (a k), hiso (a k)⟩, hft (a k)⟩
    rw [preimage_openSubspaceOfPoints_compl,
      preimage_pointsMap_preimage_pointsMap (b k) (e (a k)) T] at hM
    exact HasAtlasOfSizeLE.mono (hbound (R k) (b k ≫ e (a k)) (hsize k)
      (pullback.snd (D.obj (a k)).hom (b k)) (hZ k) hM.2 hM.1.2
      (nonempty_completionSheaf_pullback_iso T g _ (e (a k)) (β (a k)) (hβ (a k)) (b k)).some)
      (le_max_left _ _)
  exact (isAlgebraicSpace_inverse_iff_isEffective e hcov D).1 <|
    isAlgebraicSpace_of_isPullback_of_isAlgebraicSpace_sigma (hX := fun k ↦
      isAlgebraicSpace_yoneda B S hS (R k)) hcovR
      ((fppfDescentDataSheafEquivalence e hcov).inverse.obj D).property.1
      ((fppfDescentDataSheafEquivalence e hcov).inverse.obj D).obj.hom Z hZ
      (fun k ↦ pullback.fst (D.obj (a k)).hom (b k) ≫ descentInclusion e hcov D (a k))
      (fun k ↦ pullback.snd (D.obj (a k)).hom (b k)) hpb
      (isAlgebraicSpace_sigma_of_size_le _ _ hμℵ hμ hKs fun k ↦
        hasAtlasOfSizeLE_yoneda (R k) ((hsize k).trans (le_max_right _ _)))
      (isAlgebraicSpace_sigma_of_size_le Z hZ hμℵ hμ hKs hZat)

end Descent.DescentData

end AlgebraicGeometry.Space

end
