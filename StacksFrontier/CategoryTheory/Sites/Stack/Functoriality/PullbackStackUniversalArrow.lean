module

public import StacksFrontier.CategoryTheory.FiberedCategory.BasedFunctorWhiskering
public import StacksFrontier.CategoryTheory.FiberedCategory.ShrinkHomsBasedCategory
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverBased
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStackEquivalence

/-!
# The pullback of a stack in groupoids as a universal arrow over `u`

Let `u : 𝒞 ⥤ 𝒟` be a functor between sites satisfying the assumptions of Sites 00XU, let
`p : 𝒮 ⥤ 𝒞` be a fibred category and let `G : u_p 𝒮 ⥤ 𝒳` be a stackification of the fibred
category `u_p 𝒮` of Stacks 04WG, so that `𝒳 = f⁻¹𝒮` (Stacks 04WJ). The composite
`c = G ∘ ι : 𝒮 ⥤ 𝒳` of `G` with the unit `ι : 𝒮 ⥤ u_p 𝒮` is a functor over `u`. This file shows,
for categories fibred in groupoids, that

* `c` is a **universal arrow** over `u`: for every stack in groupoids `𝒯` over `𝒟`, composing with
  `c` identifies the 1-morphisms `f⁻¹𝒮 ⟶ 𝒯` over `𝒟` with the functors `𝒮 ⥤ 𝒯` over `u`. This is
  the composite of Stacks 04W9 (`G` is a stackification) with Stacks 04WI (`u_p` is left adjoint to
  `u^p`), read without the pushforward `u^p 𝒯`;
* **for a stack `𝒮₂` in groupoids over `𝒞`**, composing with `c₂ : 𝒮₂ ⥤ f⁻¹𝒮₂` identifies the
  1-morphisms `𝒮 ⟶ 𝒮₂` over `𝒞` with the functors `𝒮 ⥤ f⁻¹𝒮₂` over `u`. This is Stacks 04WS (1),
  that `𝒮₂ ⟶ f_*f⁻¹𝒮₂` is an equivalence.

A functor `𝒮 ⥤ 𝒯` over `u` is a based functor from `𝒮` read over `𝒟` through `u`,
`BasedCategory.ofFunctor (p ⋙ u)`, to `𝒯`; this is how both statements are phrased.

## Main definitions

* `CategoryTheory.PullbackAdjunction.prFunctor`: a 1-morphism `𝒮 ⟶ u^p 𝒯` over `𝒞`, read as a
  functor `𝒮 ⥤ 𝒯` over `u`.
* `CategoryTheory.Comma.pullbackStackUnitBased`: the functor `c : 𝒮 ⥤ 𝒳` over `u`.

## Main results

* `CategoryTheory.PullbackAdjunction.isEquivalence_prFunctor`: those two notions agree.
* `CategoryTheory.Comma.isEquivalence_precompFunctor_pullbackStackUnitBased`: `c` is a universal
  arrow.
* `CategoryTheory.Comma.isEquivalence_postcompFunctor_pullbackStackUnitBased`: Stacks 04WS (1) in
  the form above.
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe w vc vd vs vt v₂ u₁ u₂ u₃ u₄ u₅ u₆

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.instCategoryObj

namespace PullbackAdjunction

section PrFunctor

variable {𝒞 : Type u₁} [Category.{vc} 𝒞] {𝒟 : Type u₂} [Category.{vd} 𝒟]
  {𝒮 : Type u₃} [Category.{vs} 𝒮] {𝒯 : Type u₄} [Category.{vt} 𝒯]
  (p : 𝒮 ⥤ 𝒞) (u : 𝒞 ⥤ 𝒟) (t : 𝒯 ⥤ 𝒟)

/-- A 1-morphism `𝒮 ⟶ u^p 𝒯` over `𝒞`, read as a functor `𝒮 ⥤ 𝒯` over `u`: the functor
`F ↦ F ⋙ pr`. -/
@[simps]
def prFunctor :
    morFibLeft p u t ⥤ (BasedCategory.ofFunctor (p ⋙ u) ⥤ᵇ BasedCategory.ofFunctor t) where
  obj F :=
    { toFunctor := (F.obj.toFunctor : 𝒮 ⥤ StrictPullback u t) ⋙ StrictPullback.pr u t
      w := (congrArg (fun K => (F.obj.toFunctor : 𝒮 ⥤ StrictPullback u t) ⋙ K)
          (StrictPullback.pr_comp_eq u t)).trans
        (congrArg (· ⋙ u) F.property.comp_eq) }
  map σ :=
    { toNatTrans := Functor.whiskerRight σ.hom.toNatTrans (StrictPullback.pr u t)
      isHomLift' := fun x =>
        StrictPullback.isHomLift_id_fib (σ.hom.toNatTrans.app x) (σ.hom.isHomLift' x) }

attribute [local implicit_reducible] prFunctor

/-- The functor `prFunctor p u t` is faithful. -/
instance faithful_prFunctor : (prFunctor p u t).Faithful where
  map_injective {F₁ F₂} σ τ h := by
    apply InducedCategory.hom_ext
    apply BasedNatTrans.ext
    ext x
    have hf : (σ.hom.toNatTrans.app x).fib = (τ.hom.toNatTrans.app x).fib :=
      congrArg (fun θ : (prFunctor p u t).obj F₁ ⟶ (prFunctor p u t).obj F₂ =>
        θ.toNatTrans.app x) h
    clear h
    exact StrictPullback.hom_ext_of_fib (𝟙 _) _ _ (σ.hom.isHomLift' x) (τ.hom.isHomLift' x) hf

/-- The functor `prFunctor p u t` is full. -/
instance full_prFunctor : (prFunctor p u t).Full where
  map_surjective {F₁ F₂} θ := by
    have hG₁ : (F₁.obj.toFunctor : 𝒮 ⥤ StrictPullback u t) ⋙
        StrictPullback.structureFunctor u t = p := F₁.property.comp_eq
    have hG₂ : (F₂.obj.toFunctor : 𝒮 ⥤ StrictPullback u t) ⋙
        StrictPullback.structureFunctor u t = p := F₂.property.comp_eq
    have e₁ : ∀ x, ((F₁.obj.toFunctor : 𝒮 ⥤ StrictPullback u t).obj x).base = p.obj x :=
      fun x => Functor.congr_obj hG₁ x
    have e₂ : ∀ x, ((F₂.obj.toFunctor : 𝒮 ⥤ StrictPullback u t).obj x).base = p.obj x :=
      fun x => Functor.congr_obj hG₂ x
    have hθ : ∀ x, t.IsHomLift (𝟙 (u.obj (p.obj x))) (θ.toNatTrans.app x) :=
      fun x => θ.isHomLift' x
    let σ : ∀ x : 𝒮, (F₁.obj.toFunctor : 𝒮 ⥤ StrictPullback u t).obj x ⟶
        (F₂.obj.toFunctor : 𝒮 ⥤ StrictPullback u t).obj x := fun x =>
      ⟨eqToHom ((e₁ x).trans (e₂ x).symm), θ.toNatTrans.app x, by
        have := hθ x
        exact (IsHomLift.fac' t (𝟙 (u.obj (p.obj x))) (θ.toNatTrans.app x)).trans
          (by
            simp [eqToHom_map]
            rfl)⟩
    have hnat : ∀ ⦃x y : 𝒮⦄ (f : x ⟶ y),
        (F₁.obj.toFunctor : 𝒮 ⥤ StrictPullback u t).map f ≫ σ y =
          σ x ≫ (F₂.obj.toFunctor : 𝒮 ⥤ StrictPullback u t).map f := by
      intro x y f
      refine StrictPullback.Hom.ext ?_ ?_
      · have h₁ : ((F₁.obj.toFunctor : 𝒮 ⥤ StrictPullback u t).map f).base =
            eqToHom (e₁ x) ≫ p.map f ≫ eqToHom (e₁ y).symm := Functor.congr_hom hG₁ f
        have h₂ : ((F₂.obj.toFunctor : 𝒮 ⥤ StrictPullback u t).map f).base =
            eqToHom (e₂ x) ≫ p.map f ≫ eqToHom (e₂ y).symm := Functor.congr_hom hG₂ f
        change ((F₁.obj.toFunctor : 𝒮 ⥤ StrictPullback u t).map f).base ≫
            eqToHom ((e₁ y).trans (e₂ y).symm) = eqToHom ((e₁ x).trans (e₂ x).symm) ≫
              ((F₂.obj.toFunctor : 𝒮 ⥤ StrictPullback u t).map f).base
        rw [h₁, h₂]
        simp
      · exact θ.toNatTrans.naturality f
    have hlift : ∀ x : 𝒮, (StrictPullback.structureFunctor u t).IsHomLift (𝟙 (p.obj x)) (σ x) :=
      fun x => IsHomLift.of_fac' _ _ _ (e₁ x) (e₂ x) (by simp [σ])
    refine ⟨⟨{ toNatTrans := { app := σ, naturality := hnat }, isHomLift' := hlift }⟩, ?_⟩
    apply BasedNatTrans.ext
    ext x
    rfl

variable {t} in
/-- When `p` is fibred and `t` is fibred in groupoids, every functor `𝒮 ⥤ 𝒯` over `u` is
isomorphic to one in the image of `prFunctor p u t`. -/
theorem essSurj_prFunctor [p.IsFibered] (ht : t.IsFiberedInGroupoids) :
    (prFunctor p u t).EssSurj where
  mem_essImage H := by
    have hH : H.toFunctor ⋙ t = p ⋙ u := H.w
    refine ⟨⟨⟨StrictPullback.liftFib p H.toFunctor hH, rfl⟩, ?_⟩, ⟨Iso.refl _⟩⟩
    refine ⟨rfl, fun {R T} f a b φ hφ => ?_⟩
    have := hφ.toIsHomLift
    have : (p ⋙ u).IsHomLift (u.map f) φ := Functor.isHomLift_comp_functor u f φ this
    have hHφ : t.IsHomLift (u.map f) (H.toFunctor.map φ) :=
      Functor.isHomLift_map_of_comp_eq hH (u.map f) φ
    exact isStronglyCartesian_liftFib_map p u t hH f φ hφ
      (ht.isStronglyCartesian_homLift (u.map f) (H.toFunctor.map φ))

end PrFunctor

end PullbackAdjunction

namespace Functor.FibredMor

section OfBased

variable {𝒞 : Type u₁} [Category.{vc} 𝒞] {𝒮 : Type u₃} [Category.{vs} 𝒮]
  {𝒯 : Type u₄} [Category.{vt} 𝒯] (p : 𝒮 ⥤ 𝒞) {t : 𝒯 ⥤ 𝒞}

/-- A based functor into a category fibred in groupoids, read as a 1-morphism of fibred
categories: it preserves strongly cartesian morphisms automatically. -/
@[simps]
def ofBasedFunctor (ht : t.IsFiberedInGroupoids) :
    (BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor t) ⥤ FibredMor p t where
  obj g := ⟨g.toFunctor, IsFibredOneMorphism.of_isFiberedInGroupoids ht g.w⟩
  map θ := ⟨θ.toNatTrans, θ.isHomLift'⟩

/-- The functor `ofBasedFunctor p ht` is full. -/
instance full_ofBasedFunctor (ht : t.IsFiberedInGroupoids) : (ofBasedFunctor p ht).Full where
  map_surjective σ := ⟨⟨σ.trans, σ.isHomLift⟩, rfl⟩

/-- The functor `ofBasedFunctor p ht` is faithful. -/
instance faithful_ofBasedFunctor (ht : t.IsFiberedInGroupoids) :
    (ofBasedFunctor p ht).Faithful where
  map_injective h := BasedNatTrans.ext _ _ (congrArg Hom.trans h)

/-- The functor `ofBasedFunctor p ht` is essentially surjective. -/
instance essSurj_ofBasedFunctor (ht : t.IsFiberedInGroupoids) :
    (ofBasedFunctor p ht).EssSurj where
  mem_essImage K := ⟨⟨K.functor, K.isFibredOneMorphism.comp_eq⟩, ⟨Iso.refl _⟩⟩

/-- The functor `ofBasedFunctor p ht` is an equivalence: into a category fibred in groupoids,
based functors and 1-morphisms of fibred categories agree. -/
instance isEquivalence_ofBasedFunctor (ht : t.IsFiberedInGroupoids) :
    (ofBasedFunctor p ht).IsEquivalence where

end OfBased

end Functor.FibredMor

namespace Comma

section UniversalArrow

variable {𝒞 : Type u₁} [Category.{vc} 𝒞] {𝒟 : Type u₂} [Category.{vd} 𝒟]
  {𝒮 : Type u₃} [Category.{vs} 𝒮] {𝒳 : Type u₄} [Category.{max u₂ u₃ vd vs} 𝒳]
  (p : 𝒮 ⥤ 𝒞) (u : 𝒞 ⥤ 𝒟) [p.IsFibered] [HasFiniteLimits 𝒞] [PreservesFiniteLimits u]
  {q : 𝒳 ⥤ 𝒟} [q.IsFibered] {G : pullbackLocalization p u ⥤ 𝒳}
  (hG : (pullbackProj p u).IsFibredOneMorphism q G)

/-- **The functor `c = G ∘ ι : 𝒮 ⥤ f⁻¹𝒮` over `u`**, as a based functor from `𝒮` read over `𝒟`
through `u`. -/
@[simps]
noncomputable def pullbackStackUnitBased :
    BasedCategory.ofFunctor (p ⋙ u) ⥤ᵇ BasedCategory.ofFunctor q where
  toFunctor := pullbackUnitLoc p u ⋙ G
  w := (congrArg (pullbackUnitLoc p u ⋙ ·) hG.comp_eq).trans
    (pullbackUnitLoc_comp_pullbackProj p u)

variable {𝒯 : Type u₅} [Category.{max u₂ u₃ vd vs} 𝒯] {K : GrothendieckTopology 𝒟}

/-- **`c` is a universal arrow over `u`.** Let `G : u_p 𝒮 ⥤ 𝒳` be a stackification of `u_p 𝒮`
(the clauses `hmor` and `hobj` of Stacks 02ZN). For every stack in groupoids `t : 𝒯 ⥤ 𝒟`,
composing with `c = G ∘ ι` is an equivalence from the 1-morphisms `f⁻¹𝒮 ⟶ 𝒯` over `𝒟` onto the
functors `𝒮 ⥤ 𝒯` over `u`. It is Stacks 04W9 for `G` followed by Stacks 04WI for `u`. -/
theorem isEquivalence_precompFunctor_pullbackStackUnitBased [u.Faithful]
    (hmor : ∀ (V : 𝒟) (a b : (pullbackProj p u).Fiber V),
      Presheaf.IsLocallyInjective (K.over V) (hG.morPresheafMap a b) ∧
        Presheaf.IsLocallySurjective (K.over V) (hG.morPresheafMap a b))
    (hobj : ∀ (V : 𝒟) (x' : q.Fiber V), ∃ R ∈ K V, ∀ ⦃W : 𝒟⦄ ⦃g : W ⟶ V⦄, R.arrows g →
      (Functor.fiberFunctorOfCompEq hG.comp_eq W).essImage (Functor.pullbackFiber q x' g))
    {t : 𝒯 ⥤ 𝒟} (ht : t.IsStack K) (htg : t.IsFiberedInGroupoids) :
    (BasedFunctor.precompFunctor (pullbackStackUnitBased p u hG)
      (BasedCategory.ofFunctor t)).IsEquivalence := by
  have : HasNonemptyFiniteLimits 𝒞 := ⟨fun _ => inferInstance⟩
  have : t.IsFibered := ht.isFibered
  have hu : ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J],
      PreservesLimitsOfShape J u := fun _ => inferInstance
  have := Functor.Stackification.restrict_isEquivalence hG hmor ht.isMorSheaf hobj
    ht.hasEffectiveDescent
  have : (PullbackAdjunction.restrictAlongPullbackUnit p u t hu).IsEquivalence := {}
  have := PullbackAdjunction.essSurj_prFunctor p u htg
  have : (PullbackAdjunction.prFunctor p u t).IsEquivalence := {}
  let Ψ := Functor.FibredMor.ofBasedFunctor q htg ⋙ Functor.restrictMor (q := t) hG ⋙
    (Functor.FibredMor.basedEquivalence (pullbackProj p u) t).functor ⋙
      PullbackAdjunction.restrictAlongPullbackUnit p u t hu ⋙ PullbackAdjunction.prFunctor p u t
  have e : Ψ ≅ BasedFunctor.precompFunctor (pullbackStackUnitBased p u hG)
      (BasedCategory.ofFunctor t) :=
    NatIso.ofComponents (fun _ => Iso.refl _) fun _ => by
      apply BasedNatTrans.ext
      ext x
      exact (Category.comp_id _).trans (Category.id_comp _).symm
  exact Functor.isEquivalence_of_iso e

/-- **The universal arrow, on small models.** When `f⁻¹𝒮` and `𝒯` are locally `w`-small,
composing with `c` followed by the comparison into the small model of `f⁻¹𝒮` is an equivalence
from the 1-morphisms between the small models onto the functors `𝒮 ⥤` (small model of `𝒯`) over
`u`. -/
theorem isEquivalence_precompFunctor_comp_shrinkHoms [u.Faithful]
    (hmor : ∀ (V : 𝒟) (a b : (pullbackProj p u).Fiber V),
      Presheaf.IsLocallyInjective (K.over V) (hG.morPresheafMap a b) ∧
        Presheaf.IsLocallySurjective (K.over V) (hG.morPresheafMap a b))
    (hobj : ∀ (V : 𝒟) (x' : q.Fiber V), ∃ R ∈ K V, ∀ ⦃W : 𝒟⦄ ⦃g : W ⟶ V⦄, R.arrows g →
      (Functor.fiberFunctorOfCompEq hG.comp_eq W).essImage (Functor.pullbackFiber q x' g))
    {t : 𝒯 ⥤ 𝒟} (ht : t.IsStack K) (htg : t.IsFiberedInGroupoids)
    [LocallySmall.{w} (BasedCategory.ofFunctor q).obj]
    [LocallySmall.{w} (BasedCategory.ofFunctor t).obj] :
    (BasedFunctor.precompFunctor
      (BasedFunctor.comp (pullbackStackUnitBased p u hG)
        (⟨ShrinkHoms.functor.{w} (BasedCategory.ofFunctor q).obj,
          BasedCategory.shrinkHoms_functor_comp (BasedCategory.ofFunctor q)⟩ :
          BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.shrinkHoms.{w} (BasedCategory.ofFunctor q)))
      (BasedCategory.ofFunctor t).shrinkHoms).IsEquivalence := by
  have hU := isEquivalence_precompFunctor_pullbackStackUnitBased p u hG hmor hobj ht htg
  let c := pullbackStackUnitBased p u hG
  let E := StacksRepresentableCFG.EquivalenceOver.toBasedEquivalence
    (BasedCategory.shrinkHomsEquivalenceOver.{w} (BasedCategory.ofFunctor q))
  let E' := StacksRepresentableCFG.EquivalenceOver.toBasedEquivalence
    (BasedCategory.shrinkHomsEquivalenceOver.{w} (BasedCategory.ofFunctor t))
  have h₁ : (BasedFunctor.postcompFunctor (BasedCategory.ofFunctor q) E'.inverse).IsEquivalence :=
    E'.symm.isEquivalence_postcompFunctor (BasedCategory.ofFunctor q)
  have h₂ : (BasedFunctor.postcompFunctor (BasedCategory.ofFunctor (p ⋙ u))
      E'.inverse).IsEquivalence :=
    E'.symm.isEquivalence_postcompFunctor (BasedCategory.ofFunctor (p ⋙ u))
  have h₃ : (BasedFunctor.precompFunctor c (BasedCategory.ofFunctor t).shrinkHoms ⋙
      BasedFunctor.postcompFunctor (BasedCategory.ofFunctor (p ⋙ u)) E'.inverse).IsEquivalence :=
    Functor.isEquivalence_of_iso (Iso.refl
      (BasedFunctor.postcompFunctor (BasedCategory.ofFunctor q) E'.inverse ⋙
        BasedFunctor.precompFunctor c (BasedCategory.ofFunctor t)))
  have h₄ : (BasedFunctor.precompFunctor c (BasedCategory.ofFunctor t).shrinkHoms).IsEquivalence :=
    Functor.isEquivalence_of_comp_right _
      (BasedFunctor.postcompFunctor (BasedCategory.ofFunctor (p ⋙ u)) E'.inverse)
  have h₅ := E.isEquivalence_precompFunctor (BasedCategory.ofFunctor t).shrinkHoms
  exact Functor.isEquivalence_of_iso (Iso.refl
    (BasedFunctor.precompFunctor E.functor (BasedCategory.ofFunctor t).shrinkHoms ⋙
      BasedFunctor.precompFunctor c (BasedCategory.ofFunctor t).shrinkHoms))

end UniversalArrow

section PostUnit

universe vs₂

variable {𝒞 : Type u₁} [Category.{vc} 𝒞] {𝒟 : Type u₂} [Category.{vd} 𝒟]
  {𝒮 : Type u₃} [Category.{vs} 𝒮] {𝒮₂ : Type u₅} [Category.{vs₂} 𝒮₂]
  {𝒳₂ : Type u₆} [Category.{max u₂ u₅ vd vs₂} 𝒳₂]
  (p : 𝒮 ⥤ 𝒞) (u : 𝒞 ⥤ 𝒟) {p₂ : 𝒮₂ ⥤ 𝒞} [p₂.IsFibered] [HasFiniteLimits 𝒞]
  [PreservesFiniteLimits u]
  {q₂ : 𝒳₂ ⥤ 𝒟} [q₂.IsFibered] {G₂ : pullbackLocalization p₂ u ⥤ 𝒳₂}
  (hG₂ : (pullbackProj p₂ u).IsFibredOneMorphism q₂ G₂)

/-- **Composition with `c₂ : 𝒮₂ ⥤ f⁻¹𝒮₂`**: a 1-morphism `𝒮 ⟶ 𝒮₂` over `𝒞` goes to the functor
`𝒮 ⥤ f⁻¹𝒮₂` over `u` obtained by composing with `c₂`. -/
@[simps]
noncomputable def compPullbackStackUnitBased :
    (BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p₂) ⥤
      (BasedCategory.ofFunctor (p ⋙ u) ⥤ᵇ BasedCategory.ofFunctor q₂) where
  obj F :=
    { toFunctor := F.toFunctor ⋙ (pullbackStackUnitBased p₂ u hG₂).toFunctor
      w := (congrArg (F.toFunctor ⋙ ·) (pullbackStackUnitBased p₂ u hG₂).w).trans
        (congrArg (· ⋙ u) F.w) }
  map θ :=
    { toNatTrans := Functor.whiskerRight θ.toNatTrans (pullbackStackUnitBased p₂ u hG₂).toFunctor
      isHomLift' := fun x => by
        have h₀ : (BasedCategory.ofFunctor (p₂ ⋙ u)).p.IsHomLift
            (𝟙 ((BasedCategory.ofFunctor (p ⋙ u)).p.obj x)) (θ.toNatTrans.app x) :=
          Functor.isHomLift_id_comp_functor u (θ.isHomLift' x)
        exact BasedFunctor.preserves_isHomLift (pullbackStackUnitBased p₂ u hG₂) _
          (θ.toNatTrans.app x) }

variable {J : GrothendieckTopology 𝒞} {K : GrothendieckTopology 𝒟} [u.IsContinuous J K]
  [u.IsCocontinuous J K] [u.Full] [u.Faithful]

/-- **Stacks 04WS (1), read as a universal property of `c₂`.** For a stack in groupoids `𝒮₂` over
`𝒞` with `G₂` a stackification of `u_p 𝒮₂`, composing with `c₂ : 𝒮₂ ⥤ f⁻¹𝒮₂` is an equivalence
from the 1-morphisms `𝒮 ⟶ 𝒮₂` over `𝒞` onto the functors `𝒮 ⥤ f⁻¹𝒮₂` over `u`: it is
post-composition with the equivalence `𝒮₂ ⟶ f_*f⁻¹𝒮₂` of Stacks 04WS (1). -/
theorem isEquivalence_compPullbackStackUnitBased [p.IsFibered] (hs₂ : p₂.IsStack J)
    (hq₂ : q₂.IsStack K) (hp₂g : p₂.IsFiberedInGroupoids) (hq₂g : q₂.IsFiberedInGroupoids)
    (hmor₂ : ∀ (V : 𝒟) (a b : (pullbackProj p₂ u).Fiber V),
      Presheaf.IsLocallyInjective (K.over V) (hG₂.morPresheafMap a b) ∧
        Presheaf.IsLocallySurjective (K.over V) (hG₂.morPresheafMap a b))
    (hobj₂ : ∀ (V : 𝒟) (x' : q₂.Fiber V), ∃ R ∈ K V, ∀ ⦃W : 𝒟⦄ ⦃g : W ⟶ V⦄, R.arrows g →
      (Functor.fiberFunctorOfCompEq hG₂.comp_eq W).essImage (Functor.pullbackFiber q₂ x' g)) :
    (compPullbackStackUnitBased p u hG₂).IsEquivalence := by
  let E := equivalenceOverPullbackStackCanUniv p₂ u hG₂ hs₂ hq₂ hmor₂ hobj₂
  obtain ⟨hfl, hfa⟩ := fullyFaithful_pullbackStackCanUniv p₂ u hG₂ hs₂ hq₂ hmor₂
  have hKc := isFibredOneMorphism_pullbackStackCanUniv p₂ u hG₂
  have hH : (StrictPullback.structureFunctor u q₂).IsFibredOneMorphism p₂ E.inv :=
    Functor.IsFibredOneMorphism.of_isFiberedInGroupoids hp₂g E.inv_over
  have hε : ∀ y, (StrictPullback.structureFunctor u q₂).IsHomLift
      (𝟙 ((StrictPullback.structureFunctor u q₂).obj y)) (E.counitIso.hom.app y) := by
    intro y
    refine isHomLift_id_congr_univ ?_ _ (E.counit_vertical y)
    exact (Functor.congr_obj hKc.comp_eq (E.inv.obj y)).trans (Functor.congr_obj E.inv_over y)
  let P := postcompFibredMorEquivalenceUniv (p := p) hKc hH E.counitIso hε
  have := PullbackAdjunction.essSurj_prFunctor p u hq₂g
  have : (PullbackAdjunction.prFunctor p u q₂).IsEquivalence := {}
  let Ψ := Functor.FibredMor.ofBasedFunctor p hp₂g ⋙ P.functor ⋙
    (Functor.FibredMor.basedEquivalence p (StrictPullback.structureFunctor u q₂)).functor ⋙
      PullbackAdjunction.prFunctor p u q₂
  have e : Ψ ≅ compPullbackStackUnitBased p u hG₂ :=
    NatIso.ofComponents (fun _ => Iso.refl _) fun _ => by
      apply BasedNatTrans.ext
      ext x
      exact (Category.comp_id _).trans (Category.id_comp _).symm
  exact Functor.isEquivalence_of_iso e

/-- **Stacks 04WS (1) as a universal property of `c₂`, on the small model.** When `f⁻¹𝒮₂` is
locally `w`-small, composing with `c₂` followed by the comparison into the small model of
`f⁻¹𝒮₂` is an equivalence. -/
theorem isEquivalence_compPullbackStackUnitBased_shrinkHoms [p.IsFibered] (hs₂ : p₂.IsStack J)
    (hq₂ : q₂.IsStack K) (hp₂g : p₂.IsFiberedInGroupoids) (hq₂g : q₂.IsFiberedInGroupoids)
    (hmor₂ : ∀ (V : 𝒟) (a b : (pullbackProj p₂ u).Fiber V),
      Presheaf.IsLocallyInjective (K.over V) (hG₂.morPresheafMap a b) ∧
        Presheaf.IsLocallySurjective (K.over V) (hG₂.morPresheafMap a b))
    (hobj₂ : ∀ (V : 𝒟) (x' : q₂.Fiber V), ∃ R ∈ K V, ∀ ⦃W : 𝒟⦄ ⦃g : W ⟶ V⦄, R.arrows g →
      (Functor.fiberFunctorOfCompEq hG₂.comp_eq W).essImage (Functor.pullbackFiber q₂ x' g))
    [LocallySmall.{w} (BasedCategory.ofFunctor q₂).obj] :
    (compPullbackStackUnitBased p u hG₂ ⋙
      BasedFunctor.postcompFunctor (BasedCategory.ofFunctor (p ⋙ u))
        (⟨ShrinkHoms.functor.{w} (BasedCategory.ofFunctor q₂).obj,
          BasedCategory.shrinkHoms_functor_comp (BasedCategory.ofFunctor q₂)⟩ :
          BasedCategory.ofFunctor q₂ ⥤ᵇ
            BasedCategory.shrinkHoms.{w} (BasedCategory.ofFunctor q₂))).IsEquivalence := by
  have h₁ := isEquivalence_compPullbackStackUnitBased p u hG₂ hs₂ hq₂ hp₂g hq₂g hmor₂ hobj₂
  let E := StacksRepresentableCFG.EquivalenceOver.toBasedEquivalence
    (BasedCategory.shrinkHomsEquivalenceOver.{w} (BasedCategory.ofFunctor q₂))
  have h₂ : (BasedFunctor.postcompFunctor (BasedCategory.ofFunctor (p ⋙ u))
      (⟨ShrinkHoms.functor.{w} (BasedCategory.ofFunctor q₂).obj,
          BasedCategory.shrinkHoms_functor_comp (BasedCategory.ofFunctor q₂)⟩ :
          BasedCategory.ofFunctor q₂ ⥤ᵇ
            BasedCategory.shrinkHoms.{w} (BasedCategory.ofFunctor q₂))).IsEquivalence :=
    E.isEquivalence_postcompFunctor (BasedCategory.ofFunctor (p ⋙ u))
  exact Functor.isEquivalence_trans _ _

end PostUnit

end Comma

end CategoryTheory

end
