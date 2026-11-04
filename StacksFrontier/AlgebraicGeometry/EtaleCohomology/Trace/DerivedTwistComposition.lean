module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ShortExactDerivedTrace
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow

/-!
# Composites of twisted endomorphisms

Let `P : 𝒞 ⥤ 𝒞`, `F₁ : 𝒞 ⥤ 𝒟` and `F₂ : 𝒟 ⥤ ℰ` be additive functors with `P` and `F₁` preserving
injective objects, and let `θ : P ⋙ F₁ ≅ F₁`.  A twist `τ : K ⟶ P(K)` of a bounded below complex
induces the endomorphism `CategoryTheory.Functor.derivedTwistEndo P F₁ F₂ θ K τ` of
`RF₂(RF₁(K))`; for `P = π̄_*` the direct image along the base change of the geometric Frobenius
this is the canonical action `π_X^*` on `RΓ_c(X_k̄, K)`.

This file proves that twisted endomorphisms compose: for two twists `τ : K ⟶ P(K)` and
`τ' : K ⟶ P'(K)` with comparisons `θ` and `θ'`, the composite twist
`K ⟶ P'(K) ⟶ P'(P(K))` of `P ⋙ P'`, with the composite comparison, induces the composite of the
two endomorphisms.  In particular the `m`-th power of `π_X^*` is the endomorphism induced by the
`m`-fold composite of the Frobenius twist.

It also proves that twisted endomorphisms are transported along an exact functor
`Φ : 𝒞' ⥤ 𝒞` preserving injective objects: given `κ : Φ ⋙ F₁ ≅ F₁'` and
`ρ : P' ⋙ Φ ≅ Φ ⋙ P` compatible with the comparisons, the natural isomorphism
`RF₂(RF₁'(K)) ≅ RF₂(RF₁(Φ(K)))` intertwines the endomorphism induced by a twist `τ'` of `K`
with the one induced by `Φ(τ') ≫ ρ`.  For `Φ` the direct image along an isomorphism of schemes
this compares the Frobenius actions on the compactly supported cohomology of two isomorphic
geometric fibres.

## Main definitions

* `CategoryTheory.Functor.twistCompIso`: the comparison `(P ⋙ P') ⋙ F₁ ≅ F₁` attached to `θ` and
  `θ'`.
* `CategoryTheory.Functor.twistTransportIso`: the natural isomorphism
  `RF₂(RF₁'(K)) ≅ RF₂(RF₁(Φ(K)))`.

## Main results

* `CategoryTheory.Functor.exists_twist_lift`: a twist lifts, up to quasi-isomorphism, to an
  injective resolution.
* `CategoryTheory.Functor.derivedTwistEndo_comp`: the composite twist induces the composite
  endomorphism.
* `CategoryTheory.Functor.twistTransportIso_hom_naturality`: the transport isomorphism is natural.
* `CategoryTheory.Functor.derivedTwistEndo_transport`: the transport isomorphism intertwines the
  twisted endomorphisms.

## References

* [Stacks Project, Tag 03V0](https://stacks.math.columbia.edu/tag/03V0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u₁ v₁

namespace CategoryTheory.Functor

attribute [local instance] HasDerivedCategory.standard

/-! ### Morphisms into a bounded below complex of injectives -/

section Injective

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]

/-- Two morphisms into a bounded below complex of injectives which agree in the derived category
agree in the homotopy category. -/
lemma quotient_map_eq_of_Q_map_eq {K L : CochainComplex C ℤ} (hL : CochainComplex.plus C L)
    [∀ n, Injective (L.X n)] {a b : K ⟶ L} (h : DerivedCategory.Q.map a = DerivedCategory.Q.map b) :
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map a =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map b := by
  refine (CochainComplex.Qh_map_bijective_of_injective_of_plus
    ((HomotopyCategory.quotient C _).obj K) L hL).1 ?_
  have ha := DerivedCategory.quotientCompQhIso_hom_naturality a
  have hb := DerivedCategory.quotientCompQhIso_hom_naturality b
  rw [← cancel_mono ((DerivedCategory.quotientCompQhIso C).hom.app L), ha, hb, h]

/-- Every morphism in the derived category into a bounded below complex of injectives is the
image of a morphism of complexes. -/
lemma exists_Q_map_eq {K L : CochainComplex C ℤ} (hL : CochainComplex.plus C L)
    [∀ n, Injective (L.X n)] (x : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    ∃ a : K ⟶ L, DerivedCategory.Q.map a = x := by
  obtain ⟨y, hy⟩ := (CochainComplex.Qh_map_bijective_of_injective_of_plus
    ((HomotopyCategory.quotient C _).obj K) L hL).2
      ((DerivedCategory.quotientCompQhIso C).hom.app K ≫ x ≫
        (DerivedCategory.quotientCompQhIso C).inv.app L)
  obtain ⟨a, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective y
  refine ⟨a, ?_⟩
  have ha := DerivedCategory.quotientCompQhIso_hom_naturality a
  rw [hy, Category.assoc, Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at ha
  exact ((cancel_epi _).1 ha).symm

/-- An additive functor carries two morphisms into a bounded below complex of injectives which
agree in the derived category to two morphisms which again agree there. -/
lemma Q_map_mapHomologicalComplex_eq_of_injective {D : Type*} [Category* D] [Abelian D] (G : C ⥤ D)
    [G.Additive] {K L : CochainComplex C ℤ} (hL : CochainComplex.plus C L)
    [∀ n, Injective (L.X n)] {a b : K ⟶ L} (h : DerivedCategory.Q.map a = DerivedCategory.Q.map b) :
    DerivedCategory.Q.map ((G.mapHomologicalComplex _).map a) =
      DerivedCategory.Q.map ((G.mapHomologicalComplex _).map b) :=
  DerivedCategory.Q_map_eq_of_homotopy (h := G.mapHomotopy
    (HomotopyCategory.homotopyOfEq _ _ (quotient_map_eq_of_Q_map_eq hL h)))

/-- Every bounded below complex has a quasi-isomorphism into a bounded below complex of
injectives. -/
private lemma exists_quasiIso_to_injective [EnoughInjectives C] (K : CochainComplex.Plus C) :
    ∃ (T : CochainComplex.Plus C) (ψ : K ⟶ T), QuasiIso ψ.hom ∧ ∀ n, Injective (T.obj.X n) := by
  obtain ⟨a, ha⟩ := K.property
  have : K.obj.IsStrictlyGE a := ha
  have : K.obj.IsGE a := inferInstance
  obtain ⟨R, -, -⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE a K.obj
  exact ⟨⟨R.cocomplex, R.boundedBelow⟩, ObjectProperty.homMk R.ι, R.quasiIso, R.injective⟩

/-- An additive functor carries two morphisms into `P(T)`, for `T` a bounded below complex of
injectives and `P` preserving injectives, which agree in the derived category to two morphisms
which again agree there. -/
private lemma Q_map_mapCochainComplexPlus_eq_of_injective {D : Type*} [Category* D] [Abelian D]
    (P : C ⥤ C) (G : C ⥤ D) [P.Additive] [G.Additive] [P.PreservesInjectiveObjects]
    {K T : CochainComplex.Plus C} (hT : ∀ n, Injective (T.obj.X n))
    {a b : K ⟶ P.mapCochainComplexPlus.obj T} (h : DerivedCategory.Plus.Q.map a =
      DerivedCategory.Plus.Q.map b) :
    DerivedCategory.Plus.Q.map (G.mapCochainComplexPlus.map a) =
      DerivedCategory.Plus.Q.map (G.mapCochainComplexPlus.map b) :=
  have : ∀ n, Injective ((P.mapCochainComplexPlus.obj T).obj.X n) := fun n =>
    P.injective_obj_of_injective (hT n)
  DerivedCategory.Plus.ι.map_injective
    (Q_map_mapHomologicalComplex_eq_of_injective G (P.mapCochainComplexPlus.obj T).property
      (congrArg DerivedCategory.Plus.ι.map h))

end Injective

/-! ### Lifting a twist to an injective resolution -/

section Twist

variable {C D : Type u₁} {E : Type*} [Category.{v₁} C] [Category.{v₁} D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E] [EnoughInjectives C] [EnoughInjectives D]
  (P : C ⥤ C) (F₁ : C ⥤ D) (F₂ : D ⥤ E) [P.Additive] [F₁.Additive] [F₂.Additive]
  [P.PreservesInjectiveObjects]

omit [EnoughInjectives C] [EnoughInjectives D] in
/-- **A twist lifts to an injective resolution.**  For a quasi-isomorphism `ψ : K ⟶ T` into a
bounded below complex of injectives and a twist `τ : K ⟶ P(K)` there is a twist `g` of `T` with
`τ ≫ P(ψ) = ψ ≫ g` in the derived category. -/
lemma exists_twist_lift {K T : CochainComplex.Plus C} (ψ : K ⟶ T) [QuasiIso ψ.hom]
    (hT : ∀ n, Injective (T.obj.X n)) (τ : K ⟶ P.mapCochainComplexPlus.obj K) :
    ∃ g : T ⟶ P.mapCochainComplexPlus.obj T,
      DerivedCategory.Plus.Q.map (τ ≫ P.mapCochainComplexPlus.map ψ) =
        DerivedCategory.Plus.Q.map (ψ ≫ g) := by
  have : ∀ n, Injective ((P.mapCochainComplexPlus.obj T).obj.X n) := fun n =>
    P.injective_obj_of_injective (hT n)
  obtain ⟨a, ha⟩ := exists_Q_map_eq (P.mapCochainComplexPlus.obj T).property
    (CategoryTheory.inv (DerivedCategory.Q.map ψ.hom) ≫
      DerivedCategory.Q.map (τ ≫ P.mapCochainComplexPlus.map ψ).hom)
  refine ⟨ObjectProperty.homMk a, DerivedCategory.Plus.ι.map_injective ?_⟩
  show DerivedCategory.Q.map (τ ≫ P.mapCochainComplexPlus.map ψ).hom =
    DerivedCategory.Q.map (ψ.hom ≫ a)
  rw [Functor.map_comp, ha, IsIso.hom_inv_id_assoc]

variable [F₁.PreservesInjectiveObjects]

/-! ### Composites of twists -/

variable (P' : C ⥤ C) [P'.Additive] [P'.PreservesInjectiveObjects] (θ : P ⋙ F₁ ≅ F₁)
  (θ' : P' ⋙ F₁ ≅ F₁)

/-- The comparison `(P ⋙ P') ⋙ F₁ ≅ F₁` attached to `θ : P ⋙ F₁ ≅ F₁` and
`θ' : P' ⋙ F₁ ≅ F₁`: first `θ'` behind `P`, then `θ`. -/
def twistCompIso : (P ⋙ P') ⋙ F₁ ≅ F₁ :=
  Functor.associator P P' F₁ ≪≫ Functor.isoWhiskerLeft P θ' ≪≫ θ

omit [EnoughInjectives C] [EnoughInjectives D] [F₁.PreservesInjectiveObjects] in
/-- Pasting a commutative square into a composite. -/
private lemma comp_comp_eq_of_comm {A : Type*} [Category* A] {W X Y Y' Z V : A} (a : W ⟶ X)
    (x : X ⟶ Y) (y : Y ⟶ V) (y' : X ⟶ Y') (x' : Y' ⟶ V) (z : V ⟶ Z) (h : x ≫ y = y' ≫ x') :
    (a ≫ x) ≫ (y ≫ z) = (a ≫ y') ≫ (x' ≫ z) := by
  simp only [Category.assoc, reassoc_of% h]

omit [EnoughInjectives C] [EnoughInjectives D] [F₁.PreservesInjectiveObjects]
  [P.PreservesInjectiveObjects] [P'.PreservesInjectiveObjects] in
/-- At the level of chain models the composite twist induces the composite endomorphism. -/
lemma twistChainEndo_comp (T : CochainComplex.Plus C) (g : T ⟶ P.mapCochainComplexPlus.obj T)
    (g' : T ⟶ P'.mapCochainComplexPlus.obj T) :
    twistChainEndo (P ⋙ P') F₁ F₂ (twistCompIso P F₁ P' θ θ') T
        (g' ≫ P'.mapCochainComplexPlus.map g) =
      twistChainEndo P' F₁ F₂ θ' T g' ≫ twistChainEndo P F₁ F₂ θ T g := by
  unfold twistChainEndo
  rw [← Functor.map_comp]
  congr 1
  ext n : 2
  have hn := θ'.hom.naturality (g.hom.f n)
  dsimp at hn
  show F₁.map (g'.hom.f n ≫ P'.map (g.hom.f n)) ≫
      (𝟙 _ ≫ θ'.hom.app (P.obj (T.obj.X n)) ≫ θ.hom.app (T.obj.X n)) =
    (F₁.map (g'.hom.f n) ≫ θ'.hom.app (T.obj.X n)) ≫ (F₁.map (g.hom.f n) ≫ θ.hom.app (T.obj.X n))
  rw [Category.id_comp]
  exact (congrArg (· ≫ _) (F₁.map_comp _ _)).trans (comp_comp_eq_of_comm _ _ _ _ _ _ hn)

/-- **Twisted endomorphisms compose.**  For twists `τ : K ⟶ P(K)` and `τ' : K ⟶ P'(K)`, the
composite twist `K ⟶ P'(K) ⟶ P'(P(K))` of `P ⋙ P'` induces, with the composite comparison
`CategoryTheory.Functor.twistCompIso`, the composite of the endomorphisms induced by `τ'` and by
`τ`. -/
theorem derivedTwistEndo_comp (K : CochainComplex.Plus C) (τ : K ⟶ P.mapCochainComplexPlus.obj K)
    (τ' : K ⟶ P'.mapCochainComplexPlus.obj K) :
    derivedTwistEndo (P ⋙ P') F₁ F₂ (twistCompIso P F₁ P' θ θ') K
        (τ' ≫ P'.mapCochainComplexPlus.map τ) =
      derivedTwistEndo P' F₁ F₂ θ' K τ' ≫ derivedTwistEndo P F₁ F₂ θ K τ := by
  obtain ⟨T, ψ, _, hT⟩ := exists_quasiIso_to_injective K
  obtain ⟨g, hg⟩ := exists_twist_lift P ψ hT τ
  obtain ⟨g', hg'⟩ := exists_twist_lift P' ψ hT τ'
  have h₁ : DerivedCategory.Plus.Q.map (P'.mapCochainComplexPlus.map
        (τ ≫ P.mapCochainComplexPlus.map ψ)) =
      DerivedCategory.Plus.Q.map (P'.mapCochainComplexPlus.map (ψ ≫ g)) :=
    Q_map_mapCochainComplexPlus_eq_of_injective P P' hT hg
  have hc : DerivedCategory.Plus.Q.map ((τ' ≫ P'.mapCochainComplexPlus.map τ) ≫
        (P ⋙ P').mapCochainComplexPlus.map ψ) =
      DerivedCategory.Plus.Q.map (ψ ≫ g' ≫ P'.mapCochainComplexPlus.map g) := by
    have hc' : DerivedCategory.Plus.Q.map τ' ≫ DerivedCategory.Plus.Q.map
          (P'.mapCochainComplexPlus.map (τ ≫ P.mapCochainComplexPlus.map ψ)) =
        DerivedCategory.Plus.Q.map (ψ ≫ g') ≫
          DerivedCategory.Plus.Q.map (P'.mapCochainComplexPlus.map g) := by
      rw [h₁, Functor.map_comp P'.mapCochainComplexPlus, Functor.map_comp DerivedCategory.Plus.Q,
        ← Category.assoc, ← Functor.map_comp DerivedCategory.Plus.Q, hg']
    have e₁ : DerivedCategory.Plus.Q.map ((τ' ≫ P'.mapCochainComplexPlus.map τ) ≫
          (P ⋙ P').mapCochainComplexPlus.map ψ) = DerivedCategory.Plus.Q.map τ' ≫
          DerivedCategory.Plus.Q.map
            (P'.mapCochainComplexPlus.map (τ ≫ P.mapCochainComplexPlus.map ψ)) :=
      (congrArg DerivedCategory.Plus.Q.map (Category.assoc _ _ _)).trans
        ((DerivedCategory.Plus.Q.map_comp _ _).trans
          (congrArg (DerivedCategory.Plus.Q.map τ' ≫ ·)
            (congrArg DerivedCategory.Plus.Q.map
              (P'.mapCochainComplexPlus.map_comp τ (P.mapCochainComplexPlus.map ψ)).symm)))
    have e₂ : DerivedCategory.Plus.Q.map (ψ ≫ g' ≫ P'.mapCochainComplexPlus.map g) =
        DerivedCategory.Plus.Q.map (ψ ≫ g') ≫
          DerivedCategory.Plus.Q.map (P'.mapCochainComplexPlus.map g) := by
      rw [← Functor.map_comp, Category.assoc]
    exact e₁.trans (hc'.trans e₂.symm)
  have e₁ := twistResolutionIso_hom_comp P F₁ F₂ θ ψ hT τ g hg
  have e₂ := twistResolutionIso_hom_comp P' F₁ F₂ θ' ψ hT τ' g' hg'
  have e₃ := twistResolutionIso_hom_comp (P ⋙ P') F₁ F₂ (twistCompIso P F₁ P' θ θ') ψ hT
    (τ' ≫ P'.mapCochainComplexPlus.map τ) (g' ≫ P'.mapCochainComplexPlus.map g) hc
  rw [twistChainEndo_comp, ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp] at e₃
  refine DerivedCategory.Plus.ι.map_injective ?_
  rw [Functor.map_comp, ← cancel_mono (twistResolutionIso F₁ F₂ ψ hT).hom, e₃,
    Category.assoc, e₁, reassoc_of% e₂]

/-! ### Transport of a twisted endomorphism along an exact functor -/

section Transport

variable {C' : Type u₁} [Category.{v₁} C'] [Abelian C'] [EnoughInjectives C']
  (Φ : C' ⥤ C) [Φ.Additive] [Φ.PreservesInjectiveObjects] [PreservesFiniteLimits Φ]
  [PreservesFiniteColimits Φ] (F₁' : C' ⥤ D) [F₁'.Additive] [F₁'.PreservesInjectiveObjects]
  (κ : Φ ⋙ F₁ ≅ F₁')

/-- The componentwise isomorphism `F₁(Φ(K)) ≅ F₁'(K)` induced by `κ`, as a morphism of bounded
below complexes. -/
abbrev transportCompMap (K : CochainComplex.Plus C') :
    F₁.mapCochainComplexPlus.obj (Φ.mapCochainComplexPlus.obj K) ⟶
      F₁'.mapCochainComplexPlus.obj K :=
  ObjectProperty.homMk ((NatTrans.mapHomologicalComplex κ.hom _).app K.obj)

/-- The inverse of `CategoryTheory.Functor.transportCompMap`. -/
abbrev transportCompMapInv (K : CochainComplex.Plus C') :
    F₁'.mapCochainComplexPlus.obj K ⟶
      F₁.mapCochainComplexPlus.obj (Φ.mapCochainComplexPlus.obj K) :=
  ObjectProperty.homMk ((NatTrans.mapHomologicalComplex κ.inv _).app K.obj)

omit [EnoughInjectives C] [EnoughInjectives D] [F₁.PreservesInjectiveObjects] [EnoughInjectives C']
  [Φ.PreservesInjectiveObjects] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
  [F₁'.PreservesInjectiveObjects] in
/-- `κ` followed by `κ⁻¹`, componentwise, is the identity. -/
lemma transportCompMap_comp_inv (K : CochainComplex.Plus C') :
    transportCompMap F₁ Φ F₁' κ K ≫ transportCompMapInv F₁ Φ F₁' κ K = 𝟙 _ := by
  ext n : 2
  exact κ.hom_inv_id_app (K.obj.X n)

omit [EnoughInjectives C] [EnoughInjectives D] [F₁.PreservesInjectiveObjects] [EnoughInjectives C']
  [Φ.PreservesInjectiveObjects] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
  [F₁'.PreservesInjectiveObjects] in
/-- `κ⁻¹` followed by `κ`, componentwise, is the identity. -/
lemma transportCompMapInv_comp (K : CochainComplex.Plus C') :
    transportCompMapInv F₁ Φ F₁' κ K ≫ transportCompMap F₁ Φ F₁' κ K = 𝟙 _ := by
  ext n : 2
  exact κ.inv_hom_id_app (K.obj.X n)

private lemma comp_comp_eq_of_two_squares {A : Type*} [Category* A] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : A}
    (x : X₀ ⟶ X₁) (t' : X₁ ⟶ X₂) (ki : X₂ ⟶ X₃) (kiP : X₁ ⟶ X₄) (ki₀ : X₀ ⟶ X₅) (y : X₅ ⟶ X₄)
    (r : X₄ ⟶ X₆) (t : X₆ ⟶ X₃) (hκ : x ≫ kiP = ki₀ ≫ y) (hρ : t' ≫ ki = kiP ≫ r ≫ t) :
    (x ≫ t') ≫ ki = ki₀ ≫ (y ≫ r) ≫ t := by
  rw [Category.assoc, hρ, reassoc_of% hκ, Category.assoc]

/-- Rewriting along an isomorphism inserted between two composable morphisms. -/
private lemma eq_of_comp_iso_hom {A : Type*} [Category* A] {X₀ X₁ X₂ X₃ Y : A}
    (a : X₀ ⟶ X₁) (t : X₁ ⟶ Y) (e : X₁ ≅ X₂) (q : X₀ ⟶ X₃) (uK : X₃ ⟶ X₂)
    (lhs : X₀ ⟶ Y) (chom : X₂ ⟶ Y) (hc : chom = e.inv ≫ t) (h1 : a ≫ t = lhs)
    (h2 : a ≫ e.hom = q ≫ uK) : lhs = q ≫ uK ≫ chom := by
  rw [hc, ← reassoc_of% h2, e.hom_inv_id_assoc, h1]

omit [EnoughInjectives D] [F₁.PreservesInjectiveObjects] [PreservesFiniteLimits Φ]
  [PreservesFiniteColimits Φ] [F₁'.PreservesInjectiveObjects] in
/-- **The unit of `RF₁` at `Φ(K)` against the unit of `RΦ`.**  The unit of `RF₁` at `Φ(K)` followed
by `RF₁` of the unit of `RΦ` at `K` is `κ` followed by the unit of `RF₁'` at `K` and the comparison
`RF₁' ≅ RΦ ⋙ RF₁` attached to `κ`. -/
lemma mapCochainComplexPlusDerivedUnit_app_comp_map_unit_transport (K : CochainComplex.Plus C') :
    (mapCochainComplexPlusDerivedUnit F₁).app (Φ.mapCochainComplexPlus.obj K) ≫
        F₁.rightDerivedFunctorPlus.map ((mapCochainComplexPlusDerivedUnit Φ).app K) =
      DerivedCategory.Plus.Q.map (transportCompMap F₁ Φ F₁' κ K) ≫
        (mapCochainComplexPlusDerivedUnit F₁').app K ≫
          (Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso Φ F₁ F₁' κ).hom.app
            (DerivedCategory.Plus.Q.obj K) := by
  have h1 := mapCochainComplexPlusDerivedUnit_comp Φ F₁ (rightDerivedFunctorPlusComp Φ F₁)
    (rightDerivedFunctorPlusComp_fac Φ F₁) K
  have h2 := mapCochainComplexPlusDerivedUnit_app_comp_rightDerivedFunctorPlusIsoOfCompIso_hom
    Φ F₁ F₁' κ K
  exact eq_of_comp_iso_hom _ _ ((Stacks.EtaleCohomology.rightDerivedFunctorPlusIsoOfCompIso
    Φ F₁ F₁' κ).app _) _ _ _ _ rfl h1 h2

omit [EnoughInjectives C] [Φ.PreservesInjectiveObjects] [F₁'.PreservesInjectiveObjects] in
/-- The unit `Φ(K) ⟶ RΦ(K)` is invertible for an exact functor `Φ`. -/
lemma isIso_mapCochainComplexPlusDerivedUnit_app_of_exact (K : CochainComplex.Plus C') :
    IsIso ((mapCochainComplexPlusDerivedUnit Φ).app K) :=
  Stacks.EtaleCohomology.isIso_mapCochainComplexPlusDerivedUnit_app Φ K
    fun _ => Functor.rightAcyclic_of_exact Φ _

/-- **The transport isomorphism** `RF₂(RF₁'(K)) ≅ RF₂(RF₁(Φ(K)))` attached to an exact functor
`Φ` preserving injective objects and an isomorphism `κ : Φ ⋙ F₁ ≅ F₁'`: the comparison
`RF₁' ≅ RΦ ⋙ RF₁` followed by the inverse of the unit `Φ(K) ⟶ RΦ(K)`, which is invertible since
`Φ` is exact. -/
def twistTransportIso (K : CochainComplex.Plus C') :
    F₂.rightDerivedFunctorPlus.obj
        (F₁'.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) ≅
      F₂.rightDerivedFunctorPlus.obj (F₁.rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Q.obj (Φ.mapCochainComplexPlus.obj K))) :=
  haveI := isIso_mapCochainComplexPlusDerivedUnit_app_of_exact Φ K
  F₂.rightDerivedFunctorPlus.mapIso
    ((Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso Φ F₁ F₁' κ).app _ ≪≫
      F₁.rightDerivedFunctorPlus.mapIso (asIso ((mapCochainComplexPlusDerivedUnit Φ).app K)).symm)

omit [F₁.PreservesInjectiveObjects] [F₁'.PreservesInjectiveObjects] in
/-- The transport isomorphism is natural in the complex. -/
lemma twistTransportIso_hom_naturality {K L : CochainComplex.Plus C'} (φ : K ⟶ L) :
    F₂.rightDerivedFunctorPlus.map
        (F₁'.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map φ)) ≫
        (twistTransportIso F₁ F₂ Φ F₁' κ L).hom =
      (twistTransportIso F₁ F₂ Φ F₁' κ K).hom ≫ F₂.rightDerivedFunctorPlus.map
        (F₁.rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map (Φ.mapCochainComplexPlus.map φ))) := by
  have := isIso_mapCochainComplexPlusDerivedUnit_app_of_exact Φ K
  have := isIso_mapCochainComplexPlusDerivedUnit_app_of_exact Φ L
  have hc := (Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso Φ F₁ F₁' κ).hom.naturality
    (DerivedCategory.Plus.Q.map φ)
  have hu := (mapCochainComplexPlusDerivedUnit Φ).naturality φ
  dsimp only [Functor.comp_map, Functor.comp_obj] at hc hu
  have hu' : F₁.rightDerivedFunctorPlus.map (Φ.rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map φ)) ≫
        F₁.rightDerivedFunctorPlus.map
          (CategoryTheory.inv ((mapCochainComplexPlusDerivedUnit Φ).app L)) =
      F₁.rightDerivedFunctorPlus.map
          (CategoryTheory.inv ((mapCochainComplexPlusDerivedUnit Φ).app K)) ≫
        F₁.rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map (Φ.mapCochainComplexPlus.map φ)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    rw [IsIso.comp_inv_eq, Category.assoc, hu, IsIso.inv_hom_id_assoc]
  simp only [twistTransportIso, Functor.mapIso_hom, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    asIso_inv, ← Functor.map_comp]
  congr 1
  rw [reassoc_of% hc, hu', Category.assoc]

omit [F₁.PreservesInjectiveObjects] [F₁'.PreservesInjectiveObjects] in
/-- **Chain model of the transport isomorphism.**  On a bounded below complex of injectives, the
transport isomorphism is read off the componentwise `κ⁻¹ : F₁'(K) ≅ F₁(Φ(K))`. -/
lemma twistComparison_comp_twistTransportIso_hom (K : CochainComplex.Plus C') :
    twistComparison F₁' F₂ K ≫ (twistTransportIso F₁ F₂ Φ F₁' κ K).hom =
      DerivedCategory.Plus.Q.map (F₂.mapCochainComplexPlus.map (transportCompMapInv F₁ Φ F₁' κ K)) ≫
        twistComparison F₁ F₂ (Φ.mapCochainComplexPlus.obj K) := by
  have := isIso_mapCochainComplexPlusDerivedUnit_app_of_exact Φ K
  have h := mapCochainComplexPlusDerivedUnit_app_comp_map_unit_transport F₁ Φ F₁' κ K
  have h' : (mapCochainComplexPlusDerivedUnit F₁').app K ≫
        (Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso Φ F₁ F₁' κ).hom.app
          (DerivedCategory.Plus.Q.obj K) ≫
        F₁.rightDerivedFunctorPlus.map
          (CategoryTheory.inv ((mapCochainComplexPlusDerivedUnit Φ).app K)) =
      DerivedCategory.Plus.Q.map (transportCompMapInv F₁ Φ F₁' κ K) ≫
        (mapCochainComplexPlusDerivedUnit F₁).app (Φ.mapCochainComplexPlus.obj K) := by
    rw [← Category.assoc, ← cancel_mono (F₁.rightDerivedFunctorPlus.map
        ((mapCochainComplexPlusDerivedUnit Φ).app K)), Category.assoc, ← Functor.map_comp,
      IsIso.inv_hom_id, Functor.map_id]
    refine (Category.comp_id _).trans ?_
    rw [Category.assoc, h, ← Category.assoc, ← Functor.map_comp, transportCompMapInv_comp,
      Functor.map_id]
    exact (Category.id_comp _).symm
  have hn := (mapCochainComplexPlusDerivedUnit F₂).naturality
    (transportCompMapInv F₁ Φ F₁' κ K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [twistComparison, twistTransportIso, Functor.mapIso_hom, Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, asIso_inv, Category.assoc, ← Functor.map_comp]
  rw [h', Functor.map_comp, ← Category.assoc, ← hn, Category.assoc]

/-- **The transport isomorphism against the resolution comparisons.**  For a quasi-isomorphism
`ψ : K ⟶ T` into a bounded below complex of injectives, the transport isomorphism is read on the
injective resolutions `T` and `Φ(T)` off the componentwise `κ⁻¹`. -/
lemma twistTransportIso_hom_comp_twistResolutionIso {K T : CochainComplex.Plus C'} (ψ : K ⟶ T)
    [QuasiIso ψ.hom] (hT : ∀ n, Injective (T.obj.X n))
    [QuasiIso (Φ.mapCochainComplexPlus.map ψ).hom]
    (hΦT : ∀ n, Injective ((Φ.mapCochainComplexPlus.obj T).obj.X n)) :
    DerivedCategory.Plus.ι.map (twistTransportIso F₁ F₂ Φ F₁' κ K).hom ≫
        (twistResolutionIso F₁ F₂ (Φ.mapCochainComplexPlus.map ψ) hΦT).hom =
      (twistResolutionIso F₁' F₂ ψ hT).hom ≫
        DerivedCategory.Q.map
          (F₂.mapCochainComplexPlus.map (transportCompMapInv F₁ Φ F₁' κ T)).hom := by
  have := isIso_twistComparison F₁ F₂ (Φ.mapCochainComplexPlus.obj T) hΦT
  have := isIso_twistComparison F₁' F₂ T hT
  have hn := twistTransportIso_hom_naturality F₁ F₂ Φ F₁' κ ψ
  have hc := twistComparison_comp_twistTransportIso_hom F₁ F₂ Φ F₁' κ T
  have hc' : (twistTransportIso F₁ F₂ Φ F₁' κ T).hom ≫
      CategoryTheory.inv (twistComparison F₁ F₂ (Φ.mapCochainComplexPlus.obj T)) =
      CategoryTheory.inv (twistComparison F₁' F₂ T) ≫
        DerivedCategory.Plus.Q.map
          (F₂.mapCochainComplexPlus.map (transportCompMapInv F₁ Φ F₁' κ T)) := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, hc, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  show DerivedCategory.Plus.ι.map _ ≫ DerivedCategory.Plus.ι.map _ =
    DerivedCategory.Plus.ι.map _ ≫ DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.Q.map (F₂.mapCochainComplexPlus.map (transportCompMapInv F₁ Φ F₁' κ T)))
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  show (twistTransportIso F₁ F₂ Φ F₁' κ K).hom ≫ (F₂.rightDerivedFunctorPlus.map
      (F₁.rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map (Φ.mapCochainComplexPlus.map ψ))) ≫
        CategoryTheory.inv (twistComparison F₁ F₂ (Φ.mapCochainComplexPlus.obj T))) =
    (F₂.rightDerivedFunctorPlus.map
      (F₁'.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map ψ)) ≫
        CategoryTheory.inv (twistComparison F₁' F₂ T)) ≫
      DerivedCategory.Plus.Q.map (F₂.mapCochainComplexPlus.map (transportCompMapInv F₁ Φ F₁' κ T))
  rw [← Category.assoc, ← hn, Category.assoc, hc', Category.assoc]

variable (P' : C' ⥤ C') [P'.Additive] [P'.PreservesInjectiveObjects] (θ : P ⋙ F₁ ≅ F₁)
  (θ' : P' ⋙ F₁' ≅ F₁') (ρ : P' ⋙ Φ ≅ Φ ⋙ P)

/-- The componentwise `ρ : Φ(P'(K)) ≅ P(Φ(K))`, as a morphism of bounded below complexes. -/
abbrev transportTwistMap (K : CochainComplex.Plus C') :
    Φ.mapCochainComplexPlus.obj (P'.mapCochainComplexPlus.obj K) ⟶
      P.mapCochainComplexPlus.obj (Φ.mapCochainComplexPlus.obj K) :=
  ObjectProperty.homMk ((NatTrans.mapHomologicalComplex ρ.hom _).app K.obj)

/-- **Transport of a twisted endomorphism.**  Let `Φ : 𝒞' ⥤ 𝒞` be exact and preserve injective
objects, with `κ : Φ ⋙ F₁ ≅ F₁'` and `ρ : P' ⋙ Φ ≅ Φ ⋙ P` compatible with `θ` and `θ'`.  For a
twist `τ'` of `K`, the transport isomorphism intertwines the endomorphism induced by `τ'` with the
endomorphism induced by the twist `Φ(τ') ≫ ρ` of `Φ(K)`. -/
theorem derivedTwistEndo_transport
    (hρ : ∀ X : C', F₁.map (ρ.hom.app X) ≫ θ.hom.app (Φ.obj X) ≫ κ.hom.app X =
      κ.hom.app (P'.obj X) ≫ θ'.hom.app X)
    (K : CochainComplex.Plus C') (τ' : K ⟶ P'.mapCochainComplexPlus.obj K) :
    derivedTwistEndo P' F₁' F₂ θ' K τ' ≫ (twistTransportIso F₁ F₂ Φ F₁' κ K).hom =
      (twistTransportIso F₁ F₂ Φ F₁' κ K).hom ≫ derivedTwistEndo P F₁ F₂ θ
        (Φ.mapCochainComplexPlus.obj K)
        (Φ.mapCochainComplexPlus.map τ' ≫ transportTwistMap P Φ P' ρ K) := by
  obtain ⟨T, ψ, _, hT⟩ := exists_quasiIso_to_injective K
  have : QuasiIso (Φ.mapCochainComplexPlus.map ψ).hom :=
    inferInstanceAs (QuasiIso ((Φ.mapHomologicalComplex _).map ψ.hom))
  have hΦT : ∀ n, Injective ((Φ.mapCochainComplexPlus.obj T).obj.X n) := fun n =>
    Φ.injective_obj_of_injective (hT n)
  obtain ⟨g', hg'⟩ := exists_twist_lift P' ψ hT τ'
  let g := Φ.mapCochainComplexPlus.map g' ≫ transportTwistMap P Φ P' ρ T
  have hnat : transportTwistMap P Φ P' ρ K ≫
      P.mapCochainComplexPlus.map (Φ.mapCochainComplexPlus.map ψ) =
        Φ.mapCochainComplexPlus.map (P'.mapCochainComplexPlus.map ψ) ≫
          transportTwistMap P Φ P' ρ T := by
    ext n : 2
    exact (ρ.hom.naturality (ψ.hom.f n)).symm
  have h₁ : DerivedCategory.Plus.Q.map (Φ.mapCochainComplexPlus.map
        (τ' ≫ P'.mapCochainComplexPlus.map ψ)) =
      DerivedCategory.Plus.Q.map (Φ.mapCochainComplexPlus.map (ψ ≫ g')) :=
    Q_map_mapCochainComplexPlus_eq_of_injective P' Φ hT hg'
  have hg : DerivedCategory.Plus.Q.map ((Φ.mapCochainComplexPlus.map τ' ≫
        transportTwistMap P Φ P' ρ K) ≫ P.mapCochainComplexPlus.map
          (Φ.mapCochainComplexPlus.map ψ)) =
      DerivedCategory.Plus.Q.map (Φ.mapCochainComplexPlus.map ψ ≫ g) := by
    rw [Category.assoc, hnat, ← Category.assoc, ← Functor.map_comp, Functor.map_comp,
      h₁, ← Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp,
      Functor.map_comp, Category.assoc]
    show _ = _ ≫ DerivedCategory.Plus.Q.map
      (Φ.mapCochainComplexPlus.map g' ≫ transportTwistMap P Φ P' ρ T)
    rw [Functor.map_comp]
  have e₁ := twistResolutionIso_hom_comp P' F₁' F₂ θ' ψ hT τ' g' hg'
  have e₂ := twistResolutionIso_hom_comp P F₁ F₂ θ (Φ.mapCochainComplexPlus.map ψ) hΦT _ g hg
  have e₃ := twistTransportIso_hom_comp_twistResolutionIso F₁ F₂ Φ F₁' κ ψ hT
  have hch : twistChainEndo P' F₁' F₂ θ' T g' ≫
      F₂.mapCochainComplexPlus.map (transportCompMapInv F₁ Φ F₁' κ T) =
      F₂.mapCochainComplexPlus.map (transportCompMapInv F₁ Φ F₁' κ T) ≫
        twistChainEndo P F₁ F₂ θ (Φ.mapCochainComplexPlus.obj T) g := by
    unfold twistChainEndo
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    ext n : 2
    have hκ := κ.inv.naturality (g'.hom.f n)
    have hρn := hρ (T.obj.X n)
    dsimp at hκ hρn
    show (F₁'.map (g'.hom.f n) ≫ θ'.hom.app (T.obj.X n)) ≫ κ.inv.app (T.obj.X n) =
      κ.inv.app (T.obj.X n) ≫ (F₁.map (Φ.map (g'.hom.f n) ≫ ρ.hom.app (T.obj.X n)) ≫
        θ.hom.app (Φ.obj (T.obj.X n)))
    have hρ' : θ'.hom.app (T.obj.X n) ≫ κ.inv.app (T.obj.X n) =
        κ.inv.app (P'.obj (T.obj.X n)) ≫ F₁.map (ρ.hom.app (T.obj.X n)) ≫
          θ.hom.app (Φ.obj (T.obj.X n)) := by
      rw [← cancel_mono (κ.hom.app (T.obj.X n)), Category.assoc, Category.assoc, Category.assoc,
        hρn, Iso.inv_hom_id_app, Category.comp_id, Iso.inv_hom_id_app_assoc]
    exact (comp_comp_eq_of_two_squares _ _ _ _ _ _ _ _ hκ hρ').trans
      (congrArg (fun z => κ.inv.app (T.obj.X n) ≫ z ≫ θ.hom.app (Φ.obj (T.obj.X n)))
        (F₁.map_comp _ _).symm)
  have := isIso_twistComparison F₁ F₂ (Φ.mapCochainComplexPlus.obj T) hΦT
  refine DerivedCategory.Plus.ι.map_injective ?_
  rw [Functor.map_comp, Functor.map_comp, ← cancel_mono
    (twistResolutionIso F₁ F₂ (Φ.mapCochainComplexPlus.map ψ) hΦT).hom, Category.assoc,
    Category.assoc, e₂, reassoc_of% (e₃ hΦT), e₃ hΦT, reassoc_of% e₁]
  congr 1
  rw [← Functor.map_comp, ← Functor.map_comp, ← ObjectProperty.FullSubcategory.comp_hom,
    ← ObjectProperty.FullSubcategory.comp_hom, hch]

end Transport

end Twist

end CategoryTheory.Functor

end
