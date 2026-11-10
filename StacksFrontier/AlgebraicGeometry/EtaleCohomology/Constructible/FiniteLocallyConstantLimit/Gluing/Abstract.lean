module

public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
public import StacksFrontier.CategoryTheory.Sites.Descent.StrongTransDescentData

/-!
# Effective descent read on chosen pullbacks

Let `F` be a pseudofunctor from `LocallyDiscrete Cᵒᵖ` to `Cat` and `f i : X i ⟶ S` a family of
morphisms along which descent is effective, i.e. such that `F.toDescentData f` is an equivalence.
This file reads off the two consequences used for gluing, phrased on chosen pullbacks of the
members (Mathlib's `CategoryTheory.Pseudofunctor.DescentData'`):

* a family of morphisms between the pullbacks of two objects which is compatible on the chosen
  pullbacks is the family of pullbacks of a morphism (this only needs the functor to descent data
  to be full);
* a descent datum on the chosen pullbacks is the canonical descent datum of an object.

## Main results

* `CategoryTheory.Pseudofunctor.exists_map_eq_of_full_toDescentData` and its variant
  `CategoryTheory.Pseudofunctor.exists_map_eq_of_full_toDescentData_of_isPullback` with the
  overlaps given by pullback squares;
* `CategoryTheory.Pseudofunctor.exists_iso_of_isEquivalence_toDescentData` and its variant
  `CategoryTheory.Pseudofunctor.exists_iso_of_isEquivalence_toDescentData_of_isPullback` with the
  overlaps and triple overlaps given by pullback squares.
-/

@[expose] public section

namespace CategoryTheory

open Opposite Limits

namespace Pseudofunctor

variable {C : Type*} [Category C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat)
  {ι : Type*} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
  (sq : ∀ i j, ChosenPullback (f i) (f j))
  (sq₃ : ∀ (i₁ i₂ i₃ : ι), ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃))

variable {F} in
/-- Pulling back a morphism between pullbacks commutes with precomposing with a map of the
source object. -/
public theorem pullHom_map_comp {X₁ X₂ Y : C} {M₁ N₁ : F.obj (.mk (op X₁))}
    {M₂ : F.obj (.mk (op X₂))} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} (a : N₁ ⟶ M₁)
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    {Y' : C} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    LocallyDiscreteOpToCat.pullHom ((F.map f₁.op.toLoc).toFunctor.map a ≫ φ) g gf₁ gf₂ hgf₁
        hgf₂ =
      (F.map gf₁.op.toLoc).toFunctor.map a ≫
        LocallyDiscreteOpToCat.pullHom φ g gf₁ gf₂ hgf₁ hgf₂ := by
  simpa using pullHom_map_comp_map a (𝟙 _) φ g gf₁ gf₂ hgf₁ hgf₂

variable {F} in
/-- Pulling back a morphism between pullbacks commutes with postcomposing with a map of the
target object. -/
public theorem pullHom_comp_map {X₁ X₂ Y : C} {M₁ : F.obj (.mk (op X₁))}
    {M₂ N₂ : F.obj (.mk (op X₂))} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} (b : M₂ ⟶ N₂)
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    {Y' : C} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    LocallyDiscreteOpToCat.pullHom (φ ≫ (F.map f₂.op.toLoc).toFunctor.map b) g gf₁ gf₂ hgf₁
        hgf₂ =
      LocallyDiscreteOpToCat.pullHom φ g gf₁ gf₂ hgf₁ hgf₂ ≫
        (F.map gf₂.op.toLoc).toFunctor.map b := by
  simpa using pullHom_map_comp_map (𝟙 _) b φ g gf₁ gf₂ hgf₁ hgf₂

/-- **Morphisms glue along a family of effective descent.** A family of morphisms between the
pullbacks of two objects which is compatible on the chosen pullbacks is the family of pullbacks
of a morphism. -/
public theorem exists_map_eq_of_full_toDescentData
    [(F.toDescentData f).Full] (M N : F.obj (.mk (op S)))
    (φ : ∀ i, (F.map (f i).op.toLoc).toFunctor.obj M ⟶ (F.map (f i).op.toLoc).toFunctor.obj N)
    (hφ : ∀ i j, (F.map (sq i j).p₁.op.toLoc).toFunctor.map (φ i) ≫
        ((F.toDescentData f).obj N).hom (sq i j).p (sq i j).p₁ (sq i j).p₂
          (sq i j).hp₁ (sq i j).hp₂ =
      ((F.toDescentData f).obj M).hom (sq i j).p (sq i j).p₁ (sq i j).p₂
          (sq i j).hp₁ (sq i j).hp₂ ≫ (F.map (sq i j).p₂.op.toLoc).toFunctor.map (φ j)) :
    ∃ ψ : M ⟶ N, ∀ i, (F.map (f i).op.toLoc).toFunctor.map ψ = φ i := by
  let m : (F.toDescentData f).obj M ⟶ (F.toDescentData f).obj N :=
    { hom := φ
      comm := by
        intro Y r i j f₁ f₂ hf₁ hf₂
        obtain ⟨u, hu₁, hu₂⟩ := (sq i j).isPullback.exists_lift f₁ f₂ (by rw [hf₁, hf₂])
        have hu : u ≫ (sq i j).p = r := by rw [← (sq i j).hp₁, ← Category.assoc, hu₁, hf₁]
        rw [← ((F.toDescentData f).obj N).pullHom_hom u (sq i j).p r hu (sq i j).p₁ (sq i j).p₂
            (sq i j).hp₁ (sq i j).hp₂ f₁ f₂ hu₁ hu₂,
          ← ((F.toDescentData f).obj M).pullHom_hom u (sq i j).p r hu (sq i j).p₁ (sq i j).p₂
            (sq i j).hp₁ (sq i j).hp₂ f₁ f₂ hu₁ hu₂]
        have h1 := pullHom_map_comp (φ i)
          (((F.toDescentData f).obj N).hom (sq i j).p (sq i j).p₁ (sq i j).p₂
            (sq i j).hp₁ (sq i j).hp₂) u f₁ f₂ hu₁ hu₂
        have h2 := pullHom_comp_map (φ j)
          (((F.toDescentData f).obj M).hom (sq i j).p (sq i j).p₁ (sq i j).p₂
            (sq i j).hp₁ (sq i j).hp₂) u f₁ f₂ hu₁ hu₂
        exact h1.symm.trans ((congrArg (fun z => LocallyDiscreteOpToCat.pullHom z u f₁ f₂
          hu₁ hu₂) (hφ i j)).trans h2) }
  obtain ⟨ψ, hψ⟩ := (F.toDescentData f).map_surjective m
  refine ⟨ψ, fun i => ?_⟩
  have h1 : ((F.toDescentData f).map ψ).hom i = m.hom i := by rw [hψ]
  exact h1

/-- **Morphisms glue along a family of effective descent**, with the overlaps given by pullback
squares `O i j` and their structure morphisms `r i j` to `S`. -/
public theorem exists_map_eq_of_full_toDescentData_of_isPullback
    [(F.toDescentData f).Full] (M N : F.obj (.mk (op S)))
    (O : ι → ι → C) (p : ∀ i j, O i j ⟶ X i) (q : ∀ i j, O i j ⟶ X j) (r : ∀ i j, O i j ⟶ S)
    (hO : ∀ i j, IsPullback (p i j) (q i j) (f i) (f j))
    (hr₁ : ∀ i j, p i j ≫ f i = r i j) (hr₂ : ∀ i j, q i j ≫ f j = r i j)
    (φ : ∀ i, (F.map (f i).op.toLoc).toFunctor.obj M ⟶ (F.map (f i).op.toLoc).toFunctor.obj N)
    (hφ : ∀ i j, (F.map (p i j).op.toLoc).toFunctor.map (φ i) ≫
        ((F.toDescentData f).obj N).hom (r i j) (p i j) (q i j) (hr₁ i j) (hr₂ i j) =
      ((F.toDescentData f).obj M).hom (r i j) (p i j) (q i j) (hr₁ i j) (hr₂ i j) ≫
        (F.map (q i j).op.toLoc).toFunctor.map (φ j)) :
    ∃ ψ : M ⟶ N, ∀ i, (F.map (f i).op.toLoc).toFunctor.map ψ = φ i :=
  exists_map_eq_of_full_toDescentData F f
    (fun i j => ChosenPullback.mk (O i j) (p i j) (q i j) (hO i j).w (hO i j).isLimit
      (r i j) (hr₁ i j)) M N φ hφ

/-- **Descent data on chosen pullbacks are effective along a family of effective descent.** -/
public theorem exists_iso_of_isEquivalence_toDescentData
    [(F.toDescentData f).IsEquivalence] (D : F.DescentData' sq sq₃) :
    ∃ (M : F.obj (.mk (op S))) (ε : ∀ i, (F.map (f i).op.toLoc).toFunctor.obj M ≅ D.obj i),
      ∀ i j, (F.map (sq i j).p₁.op.toLoc).toFunctor.map (ε i).hom ≫ D.hom i j =
        ((F.toDescentData f).obj M).hom (sq i j).p (sq i j).p₁ (sq i j).p₂
          (sq i j).hp₁ (sq i j).hp₂ ≫ (F.map (sq i j).p₂.op.toLoc).toFunctor.map (ε j).hom := by
  obtain ⟨M, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := F.toDescentData f)
    ((DescentData'.toDescentDataFunctor F sq sq₃).obj D)
  refine ⟨M, fun i => ⟨e.hom.hom i, e.inv.hom i, ?_, ?_⟩, fun i j => ?_⟩
  · exact congrArg (fun φ => DescentData.Hom.hom φ i) e.hom_inv_id
  · exact congrArg (fun φ => DescentData.Hom.hom φ i) e.inv_hom_id
  · have h := e.hom.comm (sq i j).p (sq i j).p₁ (sq i j).p₂ (sq i j).hp₁ (sq i j).hp₂
    have hD : ((DescentData'.toDescentDataFunctor F sq sq₃).obj D).hom (sq i j).p
        (sq i j).p₁ (sq i j).p₂ (sq i j).hp₁ (sq i j).hp₂ = D.hom i j :=
      DescentData'.pullHom'_p₁_p₂ D.hom i j
    rw [hD] at h
    exact h

/-- A family of isomorphisms on the chosen pullbacks satisfying the cocycle condition on the
chosen threefold pullbacks is a descent datum: the normalization on the diagonal follows from the
cocycle condition, the isomorphisms being invertible. -/
public def descentDataPrimeOfIso (obj : ∀ i, F.obj (.mk (op (X i))))
    (hom : ∀ i j, (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ≅
      (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j))
    (hom_comp : ∀ i₁ i₂ i₃,
      DescentData'.pullHom' (fun i j => (hom i j).hom) (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁
          (sq₃ i₁ i₂ i₃).p₂ ≫
        DescentData'.pullHom' (fun i j => (hom i j).hom) (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂
          (sq₃ i₁ i₂ i₃).p₃ =
      DescentData'.pullHom' (fun i j => (hom i j).hom) (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁
          (sq₃ i₁ i₂ i₃).p₃) :
    F.DescentData' sq sq₃ where
  obj := obj
  hom i j := (hom i j).hom
  pullHom'_hom_self i := by
    have h := DescentData'.comp_pullHom'' (fun i j => (hom i j).hom) hom_comp (f i) (𝟙 (X i))
      (𝟙 (X i)) (𝟙 (X i)) (by simp) (by simp) (by simp)
    have : IsIso (DescentData'.pullHom' (fun i j => (hom i j).hom) (f i) (𝟙 (X i)) (𝟙 (X i))
        (by simp) (by simp)) := by
      dsimp only [DescentData'.pullHom', LocallyDiscreteOpToCat.pullHom]
      infer_instance
    exact (cancel_mono _).mp (h.trans (Category.id_comp _).symm)
  pullHom'_hom_comp := hom_comp

/-- **Descent data on chosen pullbacks are effective along a family of effective descent**, for a
family of isomorphisms satisfying the cocycle condition. -/
public theorem exists_iso_of_isEquivalence_toDescentData_of_iso
    [(F.toDescentData f).IsEquivalence] (obj : ∀ i, F.obj (.mk (op (X i))))
    (hom : ∀ i j, (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ≅
      (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j))
    (hom_comp : ∀ i₁ i₂ i₃,
      DescentData'.pullHom' (fun i j => (hom i j).hom) (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁
          (sq₃ i₁ i₂ i₃).p₂ ≫
        DescentData'.pullHom' (fun i j => (hom i j).hom) (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂
          (sq₃ i₁ i₂ i₃).p₃ =
      DescentData'.pullHom' (fun i j => (hom i j).hom) (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁
          (sq₃ i₁ i₂ i₃).p₃) :
    ∃ (M : F.obj (.mk (op S))) (ε : ∀ i, (F.map (f i).op.toLoc).toFunctor.obj M ≅ obj i),
      ∀ i j, (F.map (sq i j).p₁.op.toLoc).toFunctor.map (ε i).hom ≫ (hom i j).hom =
        ((F.toDescentData f).obj M).hom (sq i j).p (sq i j).p₁ (sq i j).p₂
          (sq i j).hp₁ (sq i j).hp₂ ≫ (F.map (sq i j).p₂.op.toLoc).toFunctor.map (ε j).hom :=
  exists_iso_of_isEquivalence_toDescentData F f sq sq₃
    (descentDataPrimeOfIso F f sq sq₃ obj hom hom_comp)

/-- **Descent data on chosen pullbacks are effective along a family of effective descent**, for a
family of isomorphisms satisfying the cocycle condition stated with pulled back morphisms. -/
public theorem exists_iso_of_isEquivalence_toDescentData_of_iso'
    [(F.toDescentData f).IsEquivalence] (obj : ∀ i, F.obj (.mk (op (X i))))
    (hom : ∀ i j, (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ≅
      (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j))
    (hom_comp : ∀ i₁ i₂ i₃,
      LocallyDiscreteOpToCat.pullHom (hom i₁ i₂).hom (sq₃ i₁ i₂ i₃).p₁₂ (sq₃ i₁ i₂ i₃).p₁
          (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₁₂_p₁ (sq₃ i₁ i₂ i₃).p₁₂_p₂ ≫
        LocallyDiscreteOpToCat.pullHom (hom i₂ i₃).hom (sq₃ i₁ i₂ i₃).p₂₃ (sq₃ i₁ i₂ i₃).p₂
          (sq₃ i₁ i₂ i₃).p₃ (sq₃ i₁ i₂ i₃).p₂₃_p₂ (sq₃ i₁ i₂ i₃).p₂₃_p₃ =
      LocallyDiscreteOpToCat.pullHom (hom i₁ i₃).hom (sq₃ i₁ i₂ i₃).p₁₃ (sq₃ i₁ i₂ i₃).p₁
          (sq₃ i₁ i₂ i₃).p₃ (sq₃ i₁ i₂ i₃).p₁₃_p₁ (sq₃ i₁ i₂ i₃).p₁₃_p₃) :
    ∃ (M : F.obj (.mk (op S))) (ε : ∀ i, (F.map (f i).op.toLoc).toFunctor.obj M ≅ obj i),
      ∀ i j, (F.map (sq i j).p₁.op.toLoc).toFunctor.map (ε i).hom ≫ (hom i j).hom =
        ((F.toDescentData f).obj M).hom (sq i j).p (sq i j).p₁ (sq i j).p₂
          (sq i j).hp₁ (sq i j).hp₂ ≫ (F.map (sq i j).p₂.op.toLoc).toFunctor.map (ε j).hom :=
  exists_iso_of_isEquivalence_toDescentData_of_iso F f sq sq₃ obj hom (fun i₁ i₂ i₃ => by
    rw [DescentData'.pullHom'₁₂_eq_pullHom_of_chosenPullback₃,
      DescentData'.pullHom'₂₃_eq_pullHom_of_chosenPullback₃,
      DescentData'.pullHom'₁₃_eq_pullHom_of_chosenPullback₃]
    exact hom_comp i₁ i₂ i₃)

/-- **Gluing data are effective along a family of effective descent**, with the overlaps given
by pullback squares `O i j` and the triple overlaps by pullback squares `T i j k` of the
overlaps, with their maps `t₁`, `t₂`, `t₃` to the members. A family of isomorphisms between the
pullbacks of objects `obj i` to the overlaps which satisfies the cocycle condition on the triple
overlaps is the family of gluing isomorphisms of the canonical descent datum of an object. -/
public theorem exists_iso_of_isEquivalence_toDescentData_of_isPullback
    [(F.toDescentData f).IsEquivalence]
    (O : ι → ι → C) (p : ∀ i j, O i j ⟶ X i) (q : ∀ i j, O i j ⟶ X j) (r : ∀ i j, O i j ⟶ S)
    (hO : ∀ i j, IsPullback (p i j) (q i j) (f i) (f j))
    (hr₁ : ∀ i j, p i j ≫ f i = r i j) (hr₂ : ∀ i j, q i j ≫ f j = r i j)
    (T : ι → ι → ι → C) (a₁₂ : ∀ i j k, T i j k ⟶ O i j) (a₂₃ : ∀ i j k, T i j k ⟶ O j k)
    (a₁₃ : ∀ i j k, T i j k ⟶ O i k)
    (hT : ∀ i j k, IsPullback (a₁₂ i j k) (a₂₃ i j k) (q i j) (p j k))
    (t₁ : ∀ i j k, T i j k ⟶ X i) (t₂ : ∀ i j k, T i j k ⟶ X j) (t₃ : ∀ i j k, T i j k ⟶ X k)
    (h₁₂₁ : ∀ i j k, a₁₂ i j k ≫ p i j = t₁ i j k) (h₁₂₂ : ∀ i j k, a₁₂ i j k ≫ q i j = t₂ i j k)
    (h₂₃₁ : ∀ i j k, a₂₃ i j k ≫ p j k = t₂ i j k) (h₂₃₂ : ∀ i j k, a₂₃ i j k ≫ q j k = t₃ i j k)
    (h₁₃₁ : ∀ i j k, a₁₃ i j k ≫ p i k = t₁ i j k) (h₁₃₂ : ∀ i j k, a₁₃ i j k ≫ q i k = t₃ i j k)
    (obj : ∀ i, F.obj (.mk (op (X i))))
    (hom : ∀ i j, (F.map (p i j).op.toLoc).toFunctor.obj (obj i) ≅
      (F.map (q i j).op.toLoc).toFunctor.obj (obj j))
    (hom_comp : ∀ i j k,
      LocallyDiscreteOpToCat.pullHom (hom i j).hom (a₁₂ i j k) (t₁ i j k) (t₂ i j k)
          (h₁₂₁ i j k) (h₁₂₂ i j k) ≫
        LocallyDiscreteOpToCat.pullHom (hom j k).hom (a₂₃ i j k) (t₂ i j k) (t₃ i j k)
          (h₂₃₁ i j k) (h₂₃₂ i j k) =
      LocallyDiscreteOpToCat.pullHom (hom i k).hom (a₁₃ i j k) (t₁ i j k) (t₃ i j k)
          (h₁₃₁ i j k) (h₁₃₂ i j k)) :
    ∃ (M : F.obj (.mk (op S))) (ε : ∀ i, (F.map (f i).op.toLoc).toFunctor.obj M ≅ obj i),
      ∀ i j, (F.map (p i j).op.toLoc).toFunctor.map (ε i).hom ≫ (hom i j).hom =
        ((F.toDescentData f).obj M).hom (r i j) (p i j) (q i j) (hr₁ i j) (hr₂ i j) ≫
          (F.map (q i j).op.toLoc).toFunctor.map (ε j).hom :=
  exists_iso_of_isEquivalence_toDescentData_of_iso' F f
    (fun i j => ChosenPullback.mk (O i j) (p i j) (q i j) (hO i j).w (hO i j).isLimit
      (r i j) (hr₁ i j))
    (fun i j k =>
      { chosenPullback := ChosenPullback.mk (T i j k) (a₁₂ i j k) (a₂₃ i j k) (hT i j k).w
          (hT i j k).isLimit (t₂ i j k) (h₁₂₂ i j k)
        p₁ := t₁ i j k
        p₃ := t₃ i j k
        l := { f := a₁₃ i j k
               f_p₁ := h₁₃₁ i j k
               f_p₂ := h₁₃₂ i j k
               f_p := by
                 change a₁₃ i j k ≫ r i k = a₁₂ i j k ≫ r i j
                 rw [← hr₁ i k, ← hr₁ i j, ← Category.assoc, ← Category.assoc, h₁₃₁ i j k,
                   h₁₂₁ i j k] }
        hp₁ := h₁₂₁ i j k
        hp₃ := h₂₃₂ i j k })
    obj hom (fun i j k => by
      have e₂ : (ChosenPullback.mk (T i j k) (a₁₂ i j k) (a₂₃ i j k) (hT i j k).w
          (hT i j k).isLimit (t₂ i j k) (h₁₂₂ i j k)).p = t₂ i j k := rfl
      exact hom_comp i j k)

end Pseudofunctor

end CategoryTheory

end
