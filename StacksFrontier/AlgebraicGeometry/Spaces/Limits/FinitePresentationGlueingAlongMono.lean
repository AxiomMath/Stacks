module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationClosedPointsGlueing

/-!
# Glueing algebraic spaces of finite presentation along a monomorphism of the base

Let `j : Z ⟶ T` be a monomorphism of the big fppf site of `S` whose Yoneda image is of finite
presentation — for instance the inclusion of a quasi-compact open subscheme — and consider a
commuting square over `T` with vertices `N`, `U'`, `M`, `T`, together with the square over `Z`
obtained from it by replacing `U'` by its base change `U = U' ×_T Z`, the morphism `M ⟶ T`
factoring through `Z`. This file proves that if the comparison functor
`FP_T ⥤ FP_{U'} ×_{FP_N} FP_M` of the square over `T` is an equivalence, then so is the comparison
functor `FP_Z ⥤ FP_U ×_{FP_N} FP_M` of the square over `Z`.

This is what makes the case of one point of Stacks 0E92 available over the intermediate bases of
its induction, `S ∖ {s₁, …, s_{n-1}}`, which are not terminal in the site: the glueing results of
`StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueing` are proved for a terminal
base only.

The comparison is made through the extension functor `FP_Z ⥤ FP_T` along `j`, which composes the
structure morphism with `j` and is fully faithful because `j` is a monomorphism, and through base
change along `j`, which is a left inverse of it. A morphism of glueing data over `Z` is transported
to one over `T` by the canonical identifications of the iterated fibre products, and its square
condition is checked on the projections of those fibre products.

## Main definitions

* `AlgebraicGeometry.FinitePresentationSpacesOver.extend`: the extension functor along a morphism
  of the site whose Yoneda image is of finite presentation.
* `CategoryTheory.Over.transportAlong`: a morphism of base changes over `Z`, transported along a
  cartesian square to a morphism of base changes of the extensions over `T`.

## Main results

* `CategoryTheory.Over.pullback_map_map_eq_of_isPullback`: two morphisms over `Z` with equal base
  changes along `b` have extensions with equal base changes along `c`, for a cartesian square
  `b ≫ j = a ≫ c`.
* `CategoryTheory.Over.squareCondition_transportAlong`: the square condition of a pair of morphisms
  over `Z` gives the square condition of the transported pair over `T`.
* `AlgebraicGeometry.FinitePresentationSpacesOver.isEquivalence_glueingFunctor_of_mono`: **the
  comparison functor over `Z` is an equivalence when the one over `T` is.**

## References

* [Stacks Project, Tag 0E92](https://stacks.math.columbia.edu/tag/0E92)
* [Stacks Project, Tag 0E90](https://stacks.math.columbia.edu/tag/0E90)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Over

variable {C : Type*} [Category C] [HasPullbacks C]

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc

/-! ### Base change after extension along a monomorphism -/

/-- Base change along a monomorphism `k` of the extension along `k` of an object over the source
is the object itself. -/
noncomputable def pullbackMapObjIsoOfMono {U U' : C} (k : U ⟶ U') [Mono k] (A : Over U) :
    (Over.pullback k).obj ((Over.map k).obj A) ≅ A :=
  Over.isoMk
    { hom := pullback.fst _ _
      inv := pullback.lift (𝟙 _) A.hom (by simp)
      hom_inv_id := by
        apply pullback.hom_ext
        · simp
        · simp only [Category.assoc, pullback.lift_snd, Category.id_comp]
          exact (cancel_mono k).1 (by simpa using pullback.condition)
      inv_hom_id := by simp }
    (by
      simp only [Over.pullback_obj_hom, Over.map_obj_left]
      exact (cancel_mono k).1 (by simpa using pullback.condition))

/-! ### Transport along a cartesian square -/

variable {A X Z T : C} {a : A ⟶ X} {b : A ⟶ Z} {c : X ⟶ T} {j : Z ⟶ T}

/-- The comparison from the base change along `c` of the extension along `j` of an object over
`Z` to its base change along `b`, for a cartesian square `a ≫ c = b ≫ j`. -/
noncomputable def pullbackCompToPullback (H : IsPullback a b c j) (Y : Over Z) :
    Limits.pullback (Y.hom ≫ j) c ⟶ Limits.pullback Y.hom b :=
  pullback.lift (pullback.fst _ _)
    (H.lift (pullback.snd _ _) (pullback.fst _ _ ≫ Y.hom) (by
      rw [Category.assoc]; exact pullback.condition.symm)) (by simp)

/-- The comparison `pullbackCompToPullback` commutes with the first projections. -/
@[reassoc (attr := simp)]
theorem pullbackCompToPullback_fst (H : IsPullback a b c j) (Y : Over Z) :
    pullbackCompToPullback H Y ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp [pullbackCompToPullback]

/-- The comparison `pullbackCompToPullback`, followed by the second projection and `a`, is the
second projection. -/
@[reassoc (attr := simp)]
theorem pullbackCompToPullback_snd_a (H : IsPullback a b c j) (Y : Over Z) :
    pullbackCompToPullback H Y ≫ pullback.snd _ _ ≫ a = pullback.snd _ _ := by
  simp [pullbackCompToPullback]

/-- The comparison from the base change along `b` of an object over `Z` to the base change along
`c` of its extension along `j`. -/
noncomputable def pullbackToPullbackComp (H : IsPullback a b c j) (Y : Over Z) :
    Limits.pullback Y.hom b ⟶ Limits.pullback (Y.hom ≫ j) c :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ a) (by
    simp only [Category.assoc]
    rw [H.w, pullback.condition_assoc])

/-- The comparison `pullbackToPullbackComp` commutes with the first projections. -/
@[reassoc (attr := simp)]
theorem pullbackToPullbackComp_fst (H : IsPullback a b c j) (Y : Over Z) :
    pullbackToPullbackComp H Y ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp [pullbackToPullbackComp]

/-- The comparison `pullbackToPullbackComp`, followed by the second projection, is the second
projection followed by `a`. -/
@[reassoc (attr := simp)]
theorem pullbackToPullbackComp_snd (H : IsPullback a b c j) (Y : Over Z) :
    pullbackToPullbackComp H Y ≫ pullback.snd _ _ = pullback.snd _ _ ≫ a := by
  simp [pullbackToPullbackComp]

/-- The comparison `pullbackToPullbackComp` followed by `pullbackCompToPullback` is the
identity. -/
@[reassoc (attr := simp)]
theorem pullbackToPullbackComp_pullbackCompToPullback (H : IsPullback a b c j) (Y : Over Z) :
    pullbackToPullbackComp H Y ≫ pullbackCompToPullback H Y = 𝟙 _ := by
  apply pullback.hom_ext
  · simp
  · apply H.hom_ext
    · simp
    · simp [pullbackCompToPullback, pullback.condition]

/-- **Transport of a morphism of base changes along a cartesian square.** A morphism between the
base changes along `b` of two objects over `Z` gives a morphism between the base changes along `c`
of their extensions along `j`. -/
noncomputable def transportAlong (H : IsPullback a b c j) {Y Y' : Over Z}
    (α : (Over.pullback b).obj Y ⟶ (Over.pullback b).obj Y') :
    (Over.pullback c).obj ((Over.map j).obj Y) ⟶ (Over.pullback c).obj ((Over.map j).obj Y') :=
  Over.homMk (pullbackCompToPullback H Y ≫ α.left ≫ pullbackToPullbackComp H Y') (by
    have hα : α.left ≫ pullback.snd Y'.hom b = pullback.snd Y.hom b := Over.w α
    simp only [Over.pullback_obj_hom, Over.map_obj_left, Over.map_obj_hom, Category.assoc,
      pullbackToPullbackComp_snd, reassoc_of% hα, pullbackCompToPullback_snd_a])

/-- The transport of `α`, followed by the first projection, is the comparison
`pullbackCompToPullback` followed by `α` and the first projection. -/
@[reassoc (attr := simp)]
theorem transportAlong_left_fst (H : IsPullback a b c j) {Y Y' : Over Z}
    (α : (Over.pullback b).obj Y ⟶ (Over.pullback b).obj Y') :
    (transportAlong H α).left ≫ pullback.fst (Y'.hom ≫ j) c =
      pullbackCompToPullback H Y ≫ α.left ≫ pullback.fst Y'.hom b := by
  simp [transportAlong]

/-- **The base change along `c` of the extension of a morphism is the transport of its base change
along `b`.** -/
theorem pullback_map_map_eq_transportAlong (H : IsPullback a b c j) {Y Y' : Over Z}
    (f : Y ⟶ Y') :
    (Over.pullback c).map ((Over.map j).map f) = transportAlong H ((Over.pullback b).map f) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp [Over.pullback_map_left]
  · simp [transportAlong, Over.pullback_map_left]

/-- **Transport is injective**: two morphisms of base changes along `b` with the same transport
agree. -/
theorem transportAlong_injective (H : IsPullback a b c j) {Y Y' : Over Z}
    {α β : (Over.pullback b).obj Y ⟶ (Over.pullback b).obj Y'}
    (h : transportAlong H α = transportAlong H β) : α = β := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have h₁ := congrArg (fun m => pullbackToPullbackComp H Y ≫ m.left ≫ pullback.fst _ _) h
    simpa using h₁
  · have hα : α.left ≫ pullback.snd Y'.hom b = pullback.snd Y.hom b := Over.w α
    have hβ : β.left ≫ pullback.snd Y'.hom b = pullback.snd Y.hom b := Over.w β
    rw [hα, hβ]

/-- **Extension and base change along a cartesian square detect equality.** Two morphisms over
`Z` with equal base changes along `b` have extensions along `j` with equal base changes along
`c`. -/
theorem pullback_map_map_eq_of_isPullback (H : IsPullback a b c j) {Y Y' : Over Z} {f g : Y ⟶ Y'}
    (h : (Over.pullback b).map f = (Over.pullback b).map g) :
    (Over.pullback c).map ((Over.map j).map f) = (Over.pullback c).map ((Over.map j).map g) := by
  rw [pullback_map_map_eq_transportAlong H, pullback_map_map_eq_transportAlong H, h]

/-! ### The square condition after transport -/

section Square

variable {U U' M N : C} [Mono j] {k : U ⟶ U'} {u : U ⟶ Z} {u' : U' ⟶ T} {mZ : M ⟶ Z}
  {m : M ⟶ T} {nU : N ⟶ U} {nU' : N ⟶ U'} {nM : N ⟶ M}

omit [HasPullbacks C] in
/-- The cartesian square exhibiting `M` as its own base change along the monomorphism `j`, when
`M ⟶ T` factors through `j`. -/
theorem isPullback_id_of_mono (hm : mZ ≫ j = m) : IsPullback (𝟙 M) mZ m j :=
  IsPullback.of_horiz_isIso_mono ⟨by simp [hm]⟩

/-- **The square condition is transported along the extension.** Let `U = U' ×_T Z` and let
`M ⟶ T` factor through `Z`. If a pair of morphisms of base changes over `Z` satisfies the square
condition of the square `nU ≫ u = nM ≫ mZ`, then the transported pair satisfies the square
condition of the square `nU' ≫ u' = nM ≫ m` over `T`. -/
theorem squareCondition_transportAlong (H : IsPullback k u u' j) (hm : mZ ≫ j = m)
    (hn : nU ≫ k = nU') (wZ : nU ≫ u = nM ≫ mZ) (wT : nU' ≫ u' = nM ≫ m) {Y Y' : Over Z}
    (α : (Over.pullback u).obj Y ⟶ (Over.pullback u).obj Y')
    (β : (Over.pullback mZ).obj Y ⟶ (Over.pullback mZ).obj Y')
    (hZ : (Over.pullback nU).map α ≫ (pullbackSquareObjIso wZ Y').hom =
      (pullbackSquareObjIso wZ Y).hom ≫ (Over.pullback nM).map β) :
    (Over.pullback nU').map (transportAlong H α) ≫
        (pullbackSquareObjIso wT ((Over.map j).obj Y')).hom =
      (pullbackSquareObjIso wT ((Over.map j).obj Y)).hom ≫
        (Over.pullback nM).map (transportAlong (isPullback_id_of_mono hm) β) := by
  -- the projection form of the square condition over `Z`
  have hZ' : pullback.fst (pullback.snd Y.hom u) nU ≫ α.left ≫ pullback.fst Y'.hom u =
      (pullbackSquareObjIso wZ Y).hom.left ≫ pullback.fst (pullback.snd Y.hom mZ) nM ≫
        β.left ≫ pullback.fst Y'.hom mZ := by
    simpa only [Over.comp_left, Category.assoc, Over.pullback_map_left, Over.pullback_obj_hom,
      pullbackSquareObjIso_hom_left_fst, pullback.lift_fst_assoc] using
      congrArg (fun t => t.left ≫ pullback.fst _ _ ≫ pullback.fst Y'.hom mZ) hZ
  have e₁ : pullbackCompToPullback H Y ≫ pullback.snd Y.hom u ≫ u =
      pullback.fst (Y.hom ≫ j) u' ≫ Y.hom := by
    simp [pullbackCompToPullback]
  -- the comparison of the two iterated fibre products
  let ω : Limits.pullback (pullback.snd (Y.hom ≫ j) u') nU' ⟶
      Limits.pullback (pullback.snd Y.hom u) nU :=
    pullback.lift (pullback.fst _ _ ≫ pullbackCompToPullback H Y) (pullback.snd _ _) (by
      apply H.hom_ext
      · simp [pullback.condition, hn]
      · apply (cancel_mono j).1
        simp only [Category.assoc]
        rw [reassoc_of% e₁, pullback.condition, pullback.condition_assoc, wT,
          reassoc_of% wZ, hm])
  have hω₁ : ω ≫ pullback.fst (pullback.snd Y.hom u) nU =
      pullback.fst _ _ ≫ pullbackCompToPullback H Y := pullback.lift_fst _ _ _
  have p₃ := pullbackSquareObjIso_hom_left_snd wT ((Over.map j).obj Y)
  have p₄ := pullbackSquareObjIso_hom_left_fst wT ((Over.map j).obj Y)
  simp only [Over.map_obj_hom, Over.map_obj_left] at p₃ p₄
  have hψD : pullbackCompToPullback (isPullback_id_of_mono hm) Y ≫ pullback.snd Y.hom mZ =
      pullback.snd (Y.hom ≫ j) m := by
    simpa using pullbackCompToPullback_snd_a (isPullback_id_of_mono hm) Y
  have hω₂ : ω ≫ (pullbackSquareObjIso wZ Y).hom.left ≫ pullback.fst (pullback.snd Y.hom mZ) nM =
      (pullbackSquareObjIso wT ((Over.map j).obj Y)).hom.left ≫
        pullback.fst (pullback.snd (Y.hom ≫ j) m) nM ≫
          pullbackCompToPullback (isPullback_id_of_mono hm) Y := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullbackSquareObjIso_hom_left_fst, reassoc_of% hω₁,
        pullbackCompToPullback_fst, p₄]
    · simp only [Category.assoc, hψD, pullback.condition, pullbackSquareObjIso_hom_left_snd_assoc,
        reassoc_of% p₃]
      simp [ω]
  have key : pullback.fst (pullback.snd (Y.hom ≫ j) u') nU' ≫ pullbackCompToPullback H Y ≫
        α.left ≫ pullback.fst Y'.hom u =
      (pullbackSquareObjIso wT ((Over.map j).obj Y)).hom.left ≫
        pullback.fst (pullback.snd (Y.hom ≫ j) m) nM ≫
          pullbackCompToPullback (isPullback_id_of_mono hm) Y ≫ β.left ≫
            pullback.fst Y'.hom mZ := by
    rw [← reassoc_of% hω₁, hZ', reassoc_of% hω₂]
  have p₁ := pullbackSquareObjIso_hom_left_fst wT ((Over.map j).obj Y')
  have p₂ := pullbackSquareObjIso_hom_left_snd wT ((Over.map j).obj Y')
  simp only [Over.map_obj_hom, Over.map_obj_left] at p₁ p₂
  apply Over.OverMorphism.ext
  refine (isPullback_pullback_snd_pullback (u := m) (q := nM)
    ((Over.map j).obj Y')).hom_ext ?_ ?_ <;>
  simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, Over.map_obj_hom,
    Over.pullback_obj_hom, Over.map_obj_left, Over.pullback_obj_left]
  · simp only [p₁, pullback.lift_fst_assoc, Category.assoc, transportAlong_left_fst]
    exact key
  · simp only [p₂, p₃, pullback.lift_snd]

end Square

end CategoryTheory.Over

namespace AlgebraicGeometry.FinitePresentationSpacesOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Extension along a morphism of finite presentation.** For a morphism `j : X ⟶ Y` of the big
fppf site of `S` whose Yoneda image is of finite presentation, an algebraic space of finite
presentation over `X` is one over `Y` through `j`. -/
noncomputable def extend {X Y : BigFppfOver B S hS} (j : X ⟶ Y)
    (hj : Space.IsFinitePresentation B S hS (yoneda.map j)) :
    FinitePresentationSpacesOver B S hS X ⥤ FinitePresentationSpacesOver B S hS Y :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Over.map (yoneda.map j))
    fun F => ⟨F.2.1, Space.isFinitePresentation_comp B S hS F.2.1
      (isAlgebraicSpace_yoneda B S hS X) (isAlgebraicSpace_yoneda B S hS Y) F.obj.hom
      (yoneda.map j) F.2.2 hj⟩

/-- The extension of a morphism, as a morphism over `Y`, is its image under `Over.map`. -/
@[simp]
theorem ι_map_extend_map {X Y : BigFppfOver B S hS} (j : X ⟶ Y)
    (hj : Space.IsFinitePresentation B S hS (yoneda.map j))
    {F G : FinitePresentationSpacesOver B S hS X} (f : F ⟶ G) :
    (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS Y)).map ((extend B S hS j hj).map f) =
      (Over.map (yoneda.map j)).map ((ObjectProperty.ι _).map f) :=
  rfl

/-- **The extension along a monomorphism is faithful.** -/
theorem extend_map_injective {X Y : BigFppfOver B S hS} (j : X ⟶ Y)
    (hj : Space.IsFinitePresentation B S hS (yoneda.map j))
    {F G : FinitePresentationSpacesOver B S hS X} {f g : F ⟶ G}
    (h : (extend B S hS j hj).map f = (extend B S hS j hj).map g) : f = g :=
  (ObjectProperty.ι _).map_injective (Over.OverMorphism.ext (congrArg (fun t => t.hom.left) h))

/-- **The extension along a monomorphism is full**: a morphism of the extensions is compatible
with the structure morphisms to `X`, which `j` does not change. -/
theorem extend_map_surjective {X Y : BigFppfOver B S hS} (j : X ⟶ Y) [Mono j]
    (hj : Space.IsFinitePresentation B S hS (yoneda.map j))
    {F G : FinitePresentationSpacesOver B S hS X}
    (h : (extend B S hS j hj).obj F ⟶ (extend B S hS j hj).obj G) :
    ∃ f : F ⟶ G, (extend B S hS j hj).map f = h := by
  have hw : h.hom.left ≫ G.obj.hom = F.obj.hom :=
    (cancel_mono (yoneda.map j)).1 ((Category.assoc _ _ _).trans (Over.w h.hom))
  exact ⟨ObjectProperty.homMk (Over.homMk h.hom.left hw),
    (ObjectProperty.ι _).map_injective (Over.OverMorphism.ext rfl)⟩

/-! ### The comparison functor over a monomorphism of the base -/

section AlongMono

variable {T Z U U' M N : BigFppfOver B S hS} {j : Z ⟶ T} {k : U ⟶ U'} {u : U ⟶ Z}
  {u' : U' ⟶ T} {mZ : M ⟶ Z} {m : M ⟶ T} {nU : N ⟶ U} {nU' : N ⟶ U'} {nM : N ⟶ M} [Mono j]
  (hj : Space.IsFinitePresentation B S hS (yoneda.map j))
  (hk : Space.IsFinitePresentation B S hS (yoneda.map k))
  (H : IsPullback k u u' j) (hm : mZ ≫ j = m) (hn : nU ≫ k = nU')
  (wZ : nU ≫ u = nM ≫ mZ) (wT : nU' ≫ u' = nM ≫ m)

omit [Mono j] in
include H in
/-- The Yoneda image of the cartesian square. -/
theorem isPullback_yoneda_map_of_isPullback :
    IsPullback (yoneda.map k) (yoneda.map u) (yoneda.map u') (yoneda.map j) :=
  H.map yoneda

include hj H hm in
/-- **The comparison functor over `Z` is faithful when the one over `T` is.** -/
theorem faithful_glueingFunctor_of_mono (hT : (glueingFunctor B S hS wT).Faithful) :
    (glueingFunctor B S hS wZ).Faithful where
  map_injective {Y Y'} {f g} h := by
    have hy := isPullback_yoneda_map_of_isPullback B S hS H
    have hu : (Over.pullback (yoneda.map u)).map f.hom = (Over.pullback (yoneda.map u)).map g.hom :=
      congrArg (fun t => t.hom.left.hom) h
    have hmZ : (Over.pullback (yoneda.map mZ)).map f.hom =
        (Over.pullback (yoneda.map mZ)).map g.hom :=
      congrArg (fun t => t.hom.right.hom) h
    refine extend_map_injective B S hS j hj (hT.map_injective ?_)
    refine ObjectProperty.hom_ext _ (Comma.hom_ext _ _ ?_ ?_)
    · exact (ObjectProperty.ι _).map_injective (Over.pullback_map_map_eq_of_isPullback hy hu)
    · exact (ObjectProperty.ι _).map_injective
        (Over.pullback_map_map_eq_of_isPullback
          (Over.isPullback_id_of_mono (j := yoneda.map j) (mZ := yoneda.map mZ)
            (by rw [← Functor.map_comp, hm])) hmZ)

include hj H hm hn in
/-- **The comparison functor over `Z` is full when the one over `T` is.** A morphism of glueing
data over `Z` is transported to one over `T` between the extensions, which comes from a morphism
of the extensions, hence from a morphism over `Z`. -/
theorem full_glueingFunctor_of_mono (hT : (glueingFunctor B S hS wT).Full) :
    (glueingFunctor B S hS wZ).Full where
  map_surjective {Y Y'} g := by
    have hy := isPullback_yoneda_map_of_isPullback B S hS H
    have hmy : yoneda.map mZ ≫ yoneda.map j = yoneda.map m := by rw [← Functor.map_comp, hm]
    have hdeg := Over.isPullback_id_of_mono (j := yoneda.map j) hmy
    have wZy : yoneda.map nU ≫ yoneda.map u = yoneda.map nM ≫ yoneda.map mZ := by
      rw [← Functor.map_comp, ← Functor.map_comp, wZ]
    have wTy : yoneda.map nU' ≫ yoneda.map u' = yoneda.map nM ≫ yoneda.map m := by
      rw [← Functor.map_comp, ← Functor.map_comp, wT]
    have hny : yoneda.map nU ≫ yoneda.map k = yoneda.map nU' := by rw [← Functor.map_comp, hn]
    -- the square condition of `g`, in the slice of presheaves
    let α : (baseChange B S hS u).obj Y ⟶ (baseChange B S hS u).obj Y' := g.hom.left
    let β : (baseChange B S hS mZ).obj Y ⟶ (baseChange B S hS mZ).obj Y' := g.hom.right
    have hZ : (Over.pullback (yoneda.map nU)).map α.hom ≫
        (Over.pullbackSquareObjIso wZy Y'.obj).hom =
          (Over.pullbackSquareObjIso wZy Y.obj).hom ≫
            (Over.pullback (yoneda.map nM)).map β.hom := by
      have h₀ : (baseChange B S hS nU).map α ≫ (baseChangeSquareIso B S hS wZ).hom.app Y' =
          (baseChangeSquareIso B S hS wZ).hom.app Y ≫ (baseChange B S hS nM).map β := g.hom.w
      have h :=
        congrArg (fun t => (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS N)).map t) h₀
      simp only [Functor.map_comp, baseChangeSquareIso_hom_app_left, ι_map_baseChange_map,
        Over.pullbackSquareIso_hom_app] at h
      exact h
    have hT' := Over.squareCondition_transportAlong hy hmy hny wZy wTy _ _ hZ
    -- the transported morphism of glueing data over `T`
    let αT : (baseChange B S hS u').obj ((extend B S hS j hj).obj Y) ⟶
        (baseChange B S hS u').obj ((extend B S hS j hj).obj Y') :=
      ObjectProperty.homMk (Over.transportAlong hy α.hom)
    let βT : (baseChange B S hS m).obj ((extend B S hS j hj).obj Y) ⟶
        (baseChange B S hS m).obj ((extend B S hS j hj).obj Y') :=
      ObjectProperty.homMk (Over.transportAlong hdeg β.hom)
    have hw : (baseChange B S hS nU').map αT ≫
        (baseChangeSquareIso B S hS wT).hom.app ((extend B S hS j hj).obj Y') =
          (baseChangeSquareIso B S hS wT).hom.app ((extend B S hS j hj).obj Y) ≫
            (baseChange B S hS nM).map βT :=
      (ObjectProperty.ι _).map_injective (by
        simp only [Functor.map_comp, baseChangeSquareIso_hom_app_left, ι_map_baseChange_map,
          Over.pullbackSquareIso_hom_app]
        exact hT')
    let g₀ : (glueingFunctor B S hS wT).obj ((extend B S hS j hj).obj Y) ⟶
        (glueingFunctor B S hS wT).obj ((extend B S hS j hj).obj Y') :=
      ObjectProperty.homMk { left := αT, right := βT, w := hw }
    obtain ⟨h₀, hh₀⟩ := hT.map_surjective g₀
    obtain ⟨h, rfl⟩ := extend_map_surjective B S hS j hj h₀
    refine ⟨h, ObjectProperty.hom_ext _ (Comma.hom_ext _ _ ?_ ?_)⟩
    · exact (ObjectProperty.ι _).map_injective (Over.transportAlong_injective hy
        ((Over.pullback_map_map_eq_transportAlong hy h.hom).symm.trans
          (congrArg (fun t => t.hom.left.hom) hh₀)))
    · exact (ObjectProperty.ι _).map_injective (Over.transportAlong_injective hdeg
        ((Over.pullback_map_map_eq_transportAlong hdeg h.hom).symm.trans
          (congrArg (fun t => t.hom.right.hom) hh₀)))

include hk H hm hn in
/-- **The comparison functor over `Z` is essentially surjective when the one over `T` is.** A
glueing datum `(A, Bm, φ)` over `Z` is extended to the datum `(A', Bm, φ')` over `T`, with `A'`
the extension of `A` along `U ⟶ U'`; a space of finite presentation over `T` realising it
restricts to one over `Z` realising `(A, Bm, φ)`, since `A'` restricts back to `A`. -/
theorem essSurj_glueingFunctor_of_mono (hT : (glueingFunctor B S hS wT).EssSurj) :
    (glueingFunctor B S hS wZ).EssSurj where
  mem_essImage T := by
    have : Mono k := H.mono_fst_of_mono
    let A := T.obj.left
    let Bm := T.obj.right
    let φ : (baseChange B S hS nU).obj A ⟶ (baseChange B S hS nM).obj Bm := T.obj.hom
    have hφ : IsIso φ := T.property
    -- the extended glueing datum over `T`
    let A' := (extend B S hS k hk).obj A
    let ε : (baseChange B S hS k).obj A' ≅ A :=
      ObjectProperty.isoMk _ (Over.pullbackMapObjIsoOfMono (yoneda.map k) A.obj)
    let F₁ := baseChangeFactorIso B S hS hn
    let φ₀ : (baseChange B S hS nU').obj A' ⟶ (baseChange B S hS nM).obj Bm :=
      F₁.hom.app A' ≫ (baseChange B S hS nU).map ε.hom ≫ φ
    have hφ₀ : IsIso φ₀ := by dsimp only [φ₀]; infer_instance
    obtain ⟨X', ⟨Ξ⟩⟩ := hT.mem_essImage
      (⟨⟨A', Bm, φ₀⟩, hφ₀⟩ : IsoComma (baseChange B S hS nU') (baseChange B S hS nM))
    let a' : (baseChange B S hS u').obj X' ≅ A' := (IsoComma.fst _ _).mapIso Ξ
    let b' : (baseChange B S hS m).obj X' ≅ Bm := (IsoComma.snd _ _).mapIso Ξ
    have hΞ : (baseChange B S hS nU').map a'.hom ≫ φ₀ =
        (baseChangeSquareIso B S hS wT).hom.app X' ≫ (baseChange B S hS nM).map b'.hom :=
      Ξ.hom.hom.w
    -- the restriction to `Z`, and its comparisons
    let Y := (baseChange B S hS j).obj X'
    have h₁ : u ≫ j = u ≫ j := rfl
    have h₂ : k ≫ u' = u ≫ j := H.w
    let G₁ := baseChangeFactorIso B S hS h₁
    let G₂ := baseChangeFactorIso B S hS h₂
    let G₃ := baseChangeFactorIso B S hS hm
    let α : (baseChange B S hS u).obj Y ≅ A :=
      (G₁.app X').symm ≪≫ G₂.app X' ≪≫ (baseChange B S hS k).mapIso a' ≪≫ ε
    let β : (baseChange B S hS mZ).obj Y ≅ Bm := (G₃.app X').symm ≪≫ b'
    refine ⟨Y, ⟨ObjectProperty.isoMk _ (Comma.isoMk α β ?_)⟩⟩
    -- the coherence of the comparison isomorphisms
    have wUT : nU ≫ (u ≫ j) = nM ≫ m := by rw [← Category.assoc, wZ, Category.assoc, hm]
    have hz₁ : nU ≫ (u ≫ j) = nU ≫ (u ≫ j) := rfl
    have hz₂ : nU' ≫ u' = nU ≫ (u ≫ j) := by rw [← hn, Category.assoc, h₂]
    have CB := baseChangeSquareIso_comp_base B S hS h₁ hm wZ wUT X'
    have CF := baseChangeSquareIso_comp_factor B S hS wUT wT hz₁ hz₂ X'
    have AS := baseChangeFactorIso_assoc B S hS hn h₂ hz₁ hz₂ X'
    have NAT := F₁.hom.naturality a'.hom
    simp only [Functor.comp_map] at NAT
    have e₁ : (baseChange B S hS nU).map (G₂.hom.app X') ≫
        (baseChange B S hS nU).map ((baseChange B S hS k).map a'.hom) ≫
          (baseChange B S hS nU).map ε.hom ≫ φ =
        (baseChangeSquareIso B S hS wUT).hom.app X' ≫ (baseChange B S hS nM).map b'.hom := by
      rw [← cancel_epi ((baseChangeFactorIso B S hS hz₁).hom.app X'), reassoc_of% AS,
        ← reassoc_of% NAT]
      have hΞ' : (baseChange B S hS nU').map a'.hom ≫ F₁.hom.app A' ≫
          (baseChange B S hS nU).map ε.hom ≫ φ =
          (baseChangeSquareIso B S hS wT).hom.app X' ≫ (baseChange B S hS nM).map b'.hom := hΞ
      rw [hΞ', reassoc_of% CF]
    have CB' : (baseChangeSquareIso B S hS wUT).hom.app X' =
        (baseChange B S hS nU).map (G₁.hom.app X') ≫
          (baseChangeSquareIso B S hS wZ).hom.app ((baseChange B S hS j).obj X') ≫
            (baseChange B S hS nM).map (G₃.inv.app X') := by
      rw [reassoc_of% CB, ← Functor.map_comp, Iso.hom_inv_id_app,
        CategoryTheory.Functor.map_id, Category.comp_id]
    change (baseChange B S hS nU).map α.hom ≫ φ =
      (baseChangeSquareIso B S hS wZ).hom.app Y ≫ (baseChange B S hS nM).map β.hom
    simp only [α, β, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_inv, Iso.app_hom,
      Functor.map_comp, Category.assoc]
    rw [e₁, CB']
    simp only [Category.assoc]
    exact Iso.inv_hom_id_assoc ((baseChange B S hS nU).mapIso (G₁.app X')) _

include hj hk H hm hn in
/-- **Glueing along a monomorphism of the base.** Let `j : Z ⟶ T` be a monomorphism of the big
fppf site of `S` whose Yoneda image is of finite presentation, let `U ⟶ U'` be the base change of
`j` along `U' ⟶ T`, and let `M ⟶ T` factor through `Z`. If the comparison functor
`FP_T ⥤ FP_{U'} ×_{FP_N} FP_M` of a square `nU' ≫ u' = nM ≫ m` is an equivalence, then so is the
comparison functor `FP_Z ⥤ FP_U ×_{FP_N} FP_M` of the square `nU ≫ u = nM ≫ mZ` over `Z`. -/
theorem isEquivalence_glueingFunctor_of_mono (hT : (glueingFunctor B S hS wT).IsEquivalence) :
    (glueingFunctor B S hS wZ).IsEquivalence :=
  ⟨faithful_glueingFunctor_of_mono B S hS (hj := hj) (H := H) (hm := hm) (wZ := wZ)
      (wT := wT) inferInstance,
    full_glueingFunctor_of_mono B S hS (hj := hj) (H := H) (hm := hm) (hn := hn)
      (wZ := wZ) (wT := wT) inferInstance,
    essSurj_glueingFunctor_of_mono B S hS (hk := hk) (H := H) (hm := hm)
      (hn := hn) (wZ := wZ) (wT := wT) inferInstance⟩

end AlongMono

end AlgebraicGeometry.FinitePresentationSpacesOver

end
