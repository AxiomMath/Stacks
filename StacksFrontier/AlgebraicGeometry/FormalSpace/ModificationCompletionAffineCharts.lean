module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.ModificationCompletionDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperCriteria

/-!
# The existence half of Stacks 0GI3 over affine charts on which the formal morphism factors

Let `X` be a locally Noetherian algebraic space over `S`, `T ⊆ |X|` closed with open complement
`U`, `f : X' ⟶ X` proper with `f⁻¹(U) ⟶ U` an isomorphism, and `(w', ŵ)` a compatible pair of
morphisms `X' ⟶ W`, `X_{/T} ⟶ W` to an algebraic space `W`. This file reduces the existence of
`w : X ⟶ W` restricting to `(w', ŵ)` to the affine situation of step B of the existence proof:
`X = Spec A` Noetherian, mapping into an affine open `Spec O` of `S`, with the formal morphism
factoring as `π ∘ ŵ₀` through an affine `W₀ = Spec C` over `Spec O`. The reduction takes as
input an atlas of `X` every point of which over `T` has an affine étale neighbourhood of that
shape.

## Main results

* `AlgebraicGeometry.Space.isIso_pullback_snd_pullback_snd_openSubspaceOfPoints`: the base change
  of a morphism which is an isomorphism over the open complement of `T` is an isomorphism over
  the open complement of the inverse image of `T`.
* `AlgebraicGeometry.Space.exists_morToModificationCompletion_eq_of_affine_charts`: the
  reduction.

## Implementation notes

Over an étale chart `r : P ⟶ V` of the atlas the base-changed data are `X' ×_X P ⟶ P` (proper,
by Stacks 04WP, and an isomorphism over the complement of the inverse image of `T`), the base
change of `w'` and the base change of `ŵ`; the affine existence statement produces a solution
over the chart, and `AlgebraicGeometry.Space.exists_morToModificationCompletion_eq_of_etale_local`
glues the solutions.

## References

* [Stacks Project, Tag 0GI3](https://stacks.math.columbia.edu/tag/0GI3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_modificationCompletionAffineCharts :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_modificationCompletionAffineCharts
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Isomorphisms over the open complement are stable under base change.** If `f : X' ⟶ X`
restricts to an isomorphism over the open complement of `T`, then its base change along
`q : G ⟶ X` restricts to an isomorphism over the open complement of the inverse image of `T`. -/
theorem isIso_pullback_snd_pullback_snd_openSubspaceOfPoints
    {X' X G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : Set (points B S hS X)} (f : X' ⟶ X)
    [IsIso (pullback.snd f (openSubspaceOfPoints B S hS X Tᶜ).ι)] (q : G ⟶ X) :
    IsIso (pullback.snd (pullback.snd f q)
      (openSubspaceOfPoints B S hS G (pointsMap B S hS G q ⁻¹' T)ᶜ).ι) := by
  set j := (openSubspaceOfPoints B S hS X Tᶜ).ι
  set jG := (openSubspaceOfPoints B S hS G (pointsMap B S hS G q ⁻¹' T)ᶜ).ι
  have hle : Subfunctor.range (jG ≫ q) ≤ openSubspaceOfPoints B S hS X Tᶜ := by
    refine range_le_openSubspaceOfPoints_of_range_subset B S hS _ _ ?_
    rintro _ ⟨z, rfl⟩
    rw [pointsMap_comp, Function.comp_apply]
    exact (range_pointsMap_ι_openSubspaceOfPoints B S hS
      (pointsMap B S hS G q ⁻¹' T)ᶜ).le ⟨z, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, g ≫ j = jG ≫ q := ⟨Subfunctor.lift (jG ≫ q) hle, Subfunctor.lift_ι _ _⟩
  obtain ⟨k, hk, hkdef⟩ : ∃ k, k ≫ f = j ∧ k = inv (pullback.snd f j) ≫ pullback.fst f j :=
    ⟨_, inv_pullback_snd_comp_pullback_fst_comp B S hS f j, rfl⟩
  have h₁ : (g ≫ k) ≫ f = jG ≫ q := by rw [Category.assoc, hk, hg]
  obtain ⟨L, hL1, hL2⟩ : ∃ L, L ≫ pullback.fst f q = g ≫ k ∧ L ≫ pullback.snd f q = jG :=
    ⟨_, pullback.lift_fst _ _ h₁, pullback.lift_snd _ _ h₁⟩
  have h₂ : L ≫ pullback.snd f q = 𝟙 _ ≫ jG := by rw [hL2, Category.id_comp]
  obtain ⟨s, hs1, hs2⟩ : ∃ s, s ≫ pullback.fst (pullback.snd f q) jG = L ∧
      s ≫ pullback.snd (pullback.snd f q) jG = 𝟙 _ :=
    ⟨_, pullback.lift_fst _ _ h₂, pullback.lift_snd _ _ h₂⟩
  refine ⟨⟨s, ?_, hs2⟩⟩
  apply pullback.hom_ext
  · rw [Category.assoc, hs1, Category.id_comp]
    apply pullback.hom_ext
    · have hl := eq_comp_inv_pullback_snd_comp_pullback_fst B S hS f j
        (pullback.fst (pullback.snd f q) jG ≫ pullback.fst f q)
        (pullback.snd (pullback.snd f q) jG ≫ g) (by
          rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
            Category.assoc, Category.assoc, hg])
      rw [Category.assoc, hL1, hl, hkdef, Category.assoc]
    · rw [Category.assoc, hL2, pullback.condition]
  · rw [Category.assoc, hs2, Category.comp_id, Category.id_comp]

/-- The base change of a compatible pair `(w', ŵ)` along `q : G ⟶ X` is compatible, once the
base change of `ŵ` is written as `completionMap q T ≫ ŵ`. -/
theorem completionMap_pullback_snd_comp_eq {X' X W G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : Set (points B S hS X)} (f : X' ⟶ X) (w' : X' ⟶ W)
    (ŵ : (completionSubfunctor B S hS X T).toFunctor ⟶ W ⋙ uliftFunctor.{u + 1})
    (hcompat : completionMap B S hS f T ≫ ŵ =
      (completionSubfunctor B S hS X' (pointsMap B S hS X' f ⁻¹' T)).ι ≫
        Functor.whiskerRight w' uliftFunctor.{u + 1})
    (q : G ⟶ X) :
    completionMap B S hS (pullback.snd f q) (pointsMap B S hS G q ⁻¹' T) ≫
        completionMap B S hS q T ≫ ŵ =
      (completionSubfunctor B S hS (pullback f q)
        (pointsMap B S hS _ (pullback.snd f q) ⁻¹' (pointsMap B S hS G q ⁻¹' T))).ι ≫
        Functor.whiskerRight (pullback.fst f q ≫ w') uliftFunctor.{u + 1} := by
  have ha : pointsMap B S hS _ (pullback.fst f q) ''
      (pointsMap B S hS _ (pullback.snd f q) ⁻¹' (pointsMap B S hS G q ⁻¹' T)) ⊆
      pointsMap B S hS X' f ⁻¹' T := by
    rintro _ ⟨x, hx, rfl⟩
    have : pointsMap B S hS X' f (pointsMap B S hS _ (pullback.fst f q) x) =
        pointsMap B S hS G q (pointsMap B S hS _ (pullback.snd f q) x) := by
      rw [← Function.comp_apply (f := pointsMap B S hS X' f), ← pointsMap_comp,
        pullback.condition, pointsMap_comp, Function.comp_apply]
    simpa only [Set.mem_preimage, this] using hx
  ext Zo y
  have h1 := congrFun (congrArg (fun α => α.app Zo) hcompat)
    ((completionSubfunctorMap B S hS (pullback.fst f q) _ _ ha).app Zo y)
  have h2 : (completionMap B S hS f T).app Zo
      ((completionSubfunctorMap B S hS (pullback.fst f q) _ _ ha).app Zo y) =
      (completionMap B S hS q T).app Zo
        ((completionMap B S hS (pullback.snd f q) (pointsMap B S hS G q ⁻¹' T)).app Zo y) :=
    Subtype.ext <| ULift.ext <|
      congrFun (congrArg (fun α => α.app Zo) (pullback.condition (f := f) (g := q))) y.1.down
  show ŵ.app Zo ((completionMap B S hS q T).app Zo
    ((completionMap B S hS (pullback.snd f q) (pointsMap B S hS G q ⁻¹' T)).app Zo y)) = _
  rw [← h2]
  exact h1

/-- **The existence half of Stacks 0GI3 over affine charts.** Let `X`, `T`, `f`, `W` be as in
Stacks 0GI3, with `f` proper and an isomorphism over the open complement of `T`, and let
`(w', ŵ)` be a compatible pair. Suppose that the affine existence statement `hlocal` holds:
over every Noetherian affine site object `V` mapping into an affine open `O` of `S`, for every
proper `f₁ : X'₁ ⟶ V` which is an isomorphism over the complement of a closed `T₁`, every
compatible pair whose formal component factors as `ŵ₀ ≫ π` through an affine site object `W₀`
over `O` comes from a morphism `V ⟶ W`. Suppose moreover that `X` has a surjective étale atlas
`p : Va ⟶ X` every point of which over `T` lies in the image of an étale chart `r : P ⟶ Va`
of that shape on which the base change of `ŵ` factors through an affine `W₀`. Then there is
`w : X ⟶ W` restricting to `w'` on `X'` and to `ŵ` on `X_{/T}`. -/
theorem exists_morToModificationCompletion_eq_of_affine_charts
    {X' X W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hW : IsAlgebraicSpace B S hS W)
    (hXnoeth : HasEtaleLocalProperty B S hS X (fun V : Scheme.{u} => IsLocallyNoetherian V))
    {T : Set (points B S hS X)} (hT : IsClosed T)
    (f : X' ⟶ X) (hfproper : IsProper B S hS f)
    (hfU : IsIso (pullback.snd f (openSubspaceOfPoints B S hS X Tᶜ).ι))
    (hlocal : ∀ (V W₀ : BigFppfOver B S hS) (O : S.Opens), IsAffineOpen O →
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      IsNoetherian ((BigFppfOver.toScheme B S hS).obj V) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj W₀) →
      Set.range (B.inclusion.map V.hom).base ⊆ (O : Set S) →
      Set.range (B.inclusion.map W₀.hom).base ⊆ (O : Set S) →
      ∀ {X'₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS X'₁ →
      ∀ {T₁ : Set (points B S hS (yoneda.obj V))}, IsClosed T₁ →
      ∀ (f₁ : X'₁ ⟶ yoneda.obj V), IsProper B S hS f₁ →
      IsIso (pullback.snd f₁ (openSubspaceOfPoints B S hS (yoneda.obj V) T₁ᶜ).ι) →
      ∀ (π : yoneda.obj W₀ ⟶ W) (w'₁ : X'₁ ⟶ W)
        (ŵ₀ : (completionSubfunctor B S hS (yoneda.obj V) T₁).toFunctor ⟶
          yoneda.obj W₀ ⋙ uliftFunctor.{u + 1}),
      completionMap B S hS f₁ T₁ ≫ ŵ₀ ≫ Functor.whiskerRight π uliftFunctor.{u + 1} =
        (completionSubfunctor B S hS X'₁ (pointsMap B S hS X'₁ f₁ ⁻¹' T₁)).ι ≫
          Functor.whiskerRight w'₁ uliftFunctor.{u + 1} →
      ∃ w₁ : yoneda.obj V ⟶ W, morToModificationCompletion B S hS f₁ T₁ W w₁ =
        (w'₁, ŵ₀ ≫ Functor.whiskerRight π uliftFunctor.{u + 1}))
    (w' : X' ⟶ W)
    (ŵ : (completionSubfunctor B S hS X T).toFunctor ⟶ W ⋙ uliftFunctor.{u + 1})
    (hcompat : completionMap B S hS f T ≫ ŵ =
      (completionSubfunctor B S hS X' (pointsMap B S hS X' f ⁻¹' T)).ι ≫
        Functor.whiskerRight w' uliftFunctor.{u + 1})
    {Va : BigFppfOver B S hS} (p : yoneda.obj Va ⟶ X)
    (hpsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (hpet : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (hcharts : ∀ v : points B S hS (yoneda.obj Va), pointsMap B S hS _ p v ∈ T →
      ∃ (P : BigFppfOver B S hS) (r : P ⟶ Va), Etale ((BigFppfOver.toScheme B S hS).map r) ∧
        pointsToScheme B S hS Va v ∈ Set.range ((BigFppfOver.toScheme B S hS).map r).base ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj P) ∧
        IsNoetherian ((BigFppfOver.toScheme B S hS).obj P) ∧
        ∃ (W₀ : BigFppfOver B S hS) (O : S.Opens), IsAffineOpen O ∧
          IsAffine ((BigFppfOver.toScheme B S hS).obj W₀) ∧
          Set.range (B.inclusion.map P.hom).base ⊆ (O : Set S) ∧
          Set.range (B.inclusion.map W₀.hom).base ⊆ (O : Set S) ∧
          ∃ (π : yoneda.obj W₀ ⟶ W)
            (ŵ₀ : (completionSubfunctor B S hS (yoneda.obj P)
              (pointsMap B S hS _ (yoneda.map r ≫ p) ⁻¹' T)).toFunctor ⟶
                yoneda.obj W₀ ⋙ uliftFunctor.{u + 1}),
            ŵ₀ ≫ Functor.whiskerRight π uliftFunctor.{u + 1} =
              completionMap B S hS (yoneda.map r ≫ p) T ≫ ŵ) :
    ∃ w : X ⟶ W, morToModificationCompletion B S hS f T W w = (w', ŵ) := by
  refine exists_morToModificationCompletion_eq_of_etale_local B S hS hX hX' hW hXnoeth hT f
    hfU w' ŵ hcompat p hpsurj hpet fun v hv => ?_
  obtain ⟨P, r, hr, hrange, hPaff, hPnoeth, W₀, O, hO, hW₀aff, hPO, hW₀O, π, ŵ₀, hŵ₀⟩ :=
    hcharts v hv
  refine ⟨P, r, hr, hrange, ?_⟩
  have hPB : IsAlgebraicSpace B S hS (pullback f (yoneda.map r ≫ p)) :=
    isAlgebraicSpace_pullback B S hS f _ hX' (isAlgebraicSpace_yoneda B S hS P) hX
  have hproper : IsProper B S hS (pullback.snd f (yoneda.map r ≫ p)) := by
    have h := isProper_comp B S hS hPB
      (isAlgebraicSpace_pullback B S hS _ f (isAlgebraicSpace_yoneda B S hS P) hX' hX)
      (isAlgebraicSpace_yoneda B S hS P) _ _
      (isProper_of_isIso B S hS (pullbackSymmetry f (yoneda.map r ≫ p)).hom)
      (isProper_pullback_fst B S hS hX' hX (isAlgebraicSpace_yoneda B S hS P) f
        (yoneda.map r ≫ p) hfproper)
    rwa [pullbackSymmetry_hom_comp_fst] at h
  have := hfU
  have hiso := isIso_pullback_snd_pullback_snd_openSubspaceOfPoints B S hS (T := T) f
    (yoneda.map r ≫ p)
  have hcomp := completionMap_pullback_snd_comp_eq B S hS f w' ŵ hcompat (yoneda.map r ≫ p)
  rw [← hŵ₀] at hcomp
  obtain ⟨w₁, hw₁⟩ := hlocal P W₀ O hO hPaff hPnoeth hW₀aff hPO hW₀O hPB
    (hT.preimage (continuous_pointsMap B S hS _)) _ hproper hiso π
    (pullback.fst f _ ≫ w') ŵ₀ hcomp
  exact ⟨w₁, congrArg Prod.fst hw₁, (congrArg Prod.snd hw₁).trans hŵ₀⟩

end Space

end AlgebraicGeometry

end
