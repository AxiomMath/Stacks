module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DerivedTwistComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DirectImageSectionsRestrictScalarsUnit

/-!
# Transport of twisted endomorphisms along a functor acyclic on the complex

`CategoryTheory.Functor.twistTransportIso` and `CategoryTheory.Functor.derivedTwistEndo_transport`
compare the twisted endomorphisms of `RF₂(RF₁'(K))` and of `RF₂(RF₁(Φ(K)))` along an *exact*
functor `Φ : 𝒞' ⥤ 𝒞` preserving injective objects, given `κ : Φ ⋙ F₁ ≅ F₁'`. Exactness of `Φ`
enters only through the invertibility of the unit `Φ(K) ⟶ RΦ(K)` at the complex `K` at hand
(and at its injective resolutions, where it is automatic). This file proves the two statements
for an additive functor `Φ` preserving injective objects and a complex `K` at which the unit is
invertible, for instance a bounded below complex of `Φ`-acyclic objects (Leray's acyclicity
lemma, [Stacks, Tag 015E]).

For `Φ` the direct image along the base change `Z_k̄ ⟶ Y_k̄` of a proper morphism `Z ⟶ Y` over a
finite field and `K` a complex of sheaves acyclic for it, this compares the Frobenius actions on
`RΓ(Y_k̄, R(i_k̄)_* K)` and `RΓ(Z_k̄, K)`, the step `Rḡ_* ∘ Rj_! = Rk_!` of the independence of
`RΓ_c` from the compactification ([Stacks, Tag 0F7I]).

## Main definitions

* `CategoryTheory.Functor.acyclicTwistTransportIso`: `RF₂(RF₁'(K)) ≅ RF₂(RF₁(Φ(K)))`.

## Main results

* `CategoryTheory.Functor.acyclicTwistTransportIso_hom_naturality`: it is natural in `K`.
* `CategoryTheory.Functor.derivedTwistEndo_acyclicTransport`: it intertwines the twisted
  endomorphisms.

## References

* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u₁ v₁

namespace CategoryTheory.Functor

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {C D : Type u₁} {E : Type*} [Category.{v₁} C] [Category.{v₁} D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E] [EnoughInjectives C] [EnoughInjectives D]
  (P : C ⥤ C) (F₁ : C ⥤ D) (F₂ : D ⥤ E) [P.Additive] [F₁.Additive] [F₂.Additive]
  [P.PreservesInjectiveObjects] [F₁.PreservesInjectiveObjects]
  {C' : Type u₁} [Category.{v₁} C'] [Abelian C'] [EnoughInjectives C']
  (Φ : C' ⥤ C) [Φ.Additive] [Φ.PreservesInjectiveObjects] (F₁' : C' ⥤ D) [F₁'.Additive]
  (κ : Φ ⋙ F₁ ≅ F₁')

/-- From `a ≫ b = c ≫ d` with `a` and `d` invertible, `b ≫ d⁻¹ = a⁻¹ ≫ c`. -/
private theorem comp_inv_eq_inv_comp_of_comp_eq {A : Type*} [Category* A] {X Y Z W : A}
    {a : X ⟶ Y} {b : Y ⟶ W} {c : X ⟶ Z} {d : Z ⟶ W} [IsIso a] [IsIso d] (h : a ≫ b = c ≫ d) :
    b ≫ CategoryTheory.inv d = CategoryTheory.inv a ≫ c := by
  rw [IsIso.eq_inv_comp, ← Category.assoc, h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

omit [EnoughInjectives D] [F₁.PreservesInjectiveObjects] in
/-- **The unit of `RF₁` at `Φ(K)` against the unit of `RΦ`**, for an arbitrary additive `Φ`
preserving injective objects: the unit of `RF₁` at `Φ(K)` followed by `RF₁` of the unit of `RΦ`
at `K` is `κ` followed by the unit of `RF₁'` at `K` and the comparison `RF₁' ≅ RΦ ⋙ RF₁`. -/
lemma mapCochainComplexPlusDerivedUnit_app_comp_map_unit_acyclicTransport
    (K : CochainComplex.Plus C') :
    (mapCochainComplexPlusDerivedUnit F₁).app (Φ.mapCochainComplexPlus.obj K) ≫
        F₁.rightDerivedFunctorPlus.map ((mapCochainComplexPlusDerivedUnit Φ).app K) =
      DerivedCategory.Plus.Q.map
          (ObjectProperty.homMk ((NatTrans.mapHomologicalComplex κ.hom _).app K.obj) :
            F₁.mapCochainComplexPlus.obj (Φ.mapCochainComplexPlus.obj K) ⟶
              F₁'.mapCochainComplexPlus.obj K) ≫
        (mapCochainComplexPlusDerivedUnit F₁').app K ≫
          (Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso Φ F₁ F₁' κ).hom.app
            (DerivedCategory.Plus.Q.obj K) := by
  have h1 := mapCochainComplexPlusDerivedUnit_comp Φ F₁ (rightDerivedFunctorPlusComp Φ F₁)
    (rightDerivedFunctorPlusComp_fac Φ F₁) K
  have h2 := mapCochainComplexPlusDerivedUnit_app_comp_rightDerivedFunctorPlusIsoOfCompIso_hom
    Φ F₁ F₁' κ K
  have key : ∀ {A : Type _} [Category A] {X₀ X₁ X₂ X₃ Y : A}
      (a : X₀ ⟶ X₁) (t : X₁ ⟶ Y) (e : X₁ ≅ X₂) (q : X₀ ⟶ X₃) (uK : X₃ ⟶ X₂)
      (lhs : X₀ ⟶ Y) (chom : X₂ ⟶ Y), chom = e.inv ≫ t → a ≫ t = lhs →
      a ≫ e.hom = q ≫ uK → lhs = q ≫ uK ≫ chom := by
    intro A _ X₀ X₁ X₂ X₃ Y a t e q uK lhs chom hc h1 h2
    rw [hc, ← reassoc_of% h2, e.hom_inv_id_assoc, h1]
  exact key _ _ ((Stacks.EtaleCohomology.rightDerivedFunctorPlusIsoOfCompIso
    Φ F₁ F₁' κ).app _) _ _ _ _ rfl h1 h2

/-- **The transport isomorphism** `RF₂(RF₁'(K)) ≅ RF₂(RF₁(Φ(K)))` attached to an additive functor
`Φ` preserving injective objects, an isomorphism `κ : Φ ⋙ F₁ ≅ F₁'` and a complex `K` at which
the unit `Φ(K) ⟶ RΦ(K)` is invertible: the comparison `RF₁' ≅ RΦ ⋙ RF₁` followed by the inverse
of that unit. -/
def acyclicTwistTransportIso (K : CochainComplex.Plus C')
    [IsIso ((mapCochainComplexPlusDerivedUnit Φ).app K)] :
    F₂.rightDerivedFunctorPlus.obj
        (F₁'.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) ≅
      F₂.rightDerivedFunctorPlus.obj (F₁.rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Q.obj (Φ.mapCochainComplexPlus.obj K))) :=
  F₂.rightDerivedFunctorPlus.mapIso
    ((Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso Φ F₁ F₁' κ).app _ ≪≫
      F₁.rightDerivedFunctorPlus.mapIso (asIso ((mapCochainComplexPlusDerivedUnit Φ).app K)).symm)

omit [F₁.PreservesInjectiveObjects] in
/-- The transport isomorphism is natural in the complex. -/
lemma acyclicTwistTransportIso_hom_naturality {K L : CochainComplex.Plus C'} (φ : K ⟶ L)
    [IsIso ((mapCochainComplexPlusDerivedUnit Φ).app K)]
    [IsIso ((mapCochainComplexPlusDerivedUnit Φ).app L)] :
    F₂.rightDerivedFunctorPlus.map
        (F₁'.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map φ)) ≫
        (acyclicTwistTransportIso F₁ F₂ Φ F₁' κ L).hom =
      (acyclicTwistTransportIso F₁ F₂ Φ F₁' κ K).hom ≫ F₂.rightDerivedFunctorPlus.map
        (F₁.rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map (Φ.mapCochainComplexPlus.map φ))) := by
  have hc := (Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso Φ F₁ F₁' κ).hom.naturality
    (DerivedCategory.Plus.Q.map φ)
  have hu := (mapCochainComplexPlusDerivedUnit Φ).naturality φ
  dsimp only [Functor.comp_map, Functor.comp_obj] at hc hu
  have hu' := congrArg F₁.rightDerivedFunctorPlus.map (comp_inv_eq_inv_comp_of_comp_eq hu.symm)
  simp only [Functor.map_comp] at hu'
  simp only [acyclicTwistTransportIso, Functor.mapIso_hom, Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, asIso_inv, ← Functor.map_comp]
  congr 1
  rw [reassoc_of% hc, hu', Category.assoc]

omit [EnoughInjectives C] [Φ.PreservesInjectiveObjects] in
/-- The unit of `RΦ` is invertible at a bounded below complex of injective objects. -/
lemma isIso_mapCochainComplexPlusDerivedUnit_app_of_injective (T : CochainComplex.Plus C')
    (hT : ∀ n, Injective (T.obj.X n)) :
    IsIso ((mapCochainComplexPlusDerivedUnit Φ).app T) :=
  Stacks.EtaleCohomology.isIso_mapCochainComplexPlusDerivedUnit_app_of_rightAcyclic Φ T
    fun n => have := hT n; rightAcyclic_of_injective Φ _

/-- A functor isomorphic to a composite of functors preserving injective objects preserves
injective objects. -/
lemma preservesInjectiveObjects_of_comp_iso {A B M : Type*} [Category* A] [Category* B]
    [Category* M] {G : A ⥤ B} {H : B ⥤ M} {L : A ⥤ M} [G.PreservesInjectiveObjects]
    [H.PreservesInjectiveObjects] (e : G ⋙ H ≅ L) : L.PreservesInjectiveObjects :=
  ⟨fun _ => Injective.of_iso (e.app _) inferInstance⟩

omit [EnoughInjectives C] [Φ.PreservesInjectiveObjects] in
/-- `Φ` carries a quasi-isomorphism between complexes at which the unit of `RΦ` is invertible to a
quasi-isomorphism. -/
lemma quasiIso_mapCochainComplexPlus_map_of_isIso_derivedUnit {K T : CochainComplex.Plus C'}
    (ψ : K ⟶ T) [QuasiIso ψ.hom] [IsIso ((mapCochainComplexPlusDerivedUnit Φ).app K)]
    [IsIso ((mapCochainComplexPlusDerivedUnit Φ).app T)] :
    QuasiIso (Φ.mapCochainComplexPlus.map ψ).hom := by
  have hψ : IsIso (DerivedCategory.Plus.Q.map ψ) :=
    have : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map ψ)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ ψ.hom).2 ‹_›
    isIso_of_fully_faithful DerivedCategory.Plus.ι _
  have hu := (mapCochainComplexPlusDerivedUnit Φ).naturality ψ
  dsimp only [Functor.comp_map, Functor.comp_obj] at hu
  have : IsIso (DerivedCategory.Plus.Q.map (Φ.mapCochainComplexPlus.map ψ)) := by
    have : IsIso (DerivedCategory.Plus.Q.map (Φ.mapCochainComplexPlus.map ψ) ≫
        (mapCochainComplexPlusDerivedUnit Φ).app T) := by
      rw [hu]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((mapCochainComplexPlusDerivedUnit Φ).app T)
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1
    (inferInstanceAs (IsIso (DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.Q.map (Φ.mapCochainComplexPlus.map ψ)))))

omit [F₁.PreservesInjectiveObjects] in
/-- **Chain model of the transport isomorphism.** On a bounded below complex of injectives, the
transport isomorphism is read off the componentwise `κ⁻¹ : F₁'(K) ≅ F₁(Φ(K))`. -/
lemma twistComparison_comp_acyclicTwistTransportIso_hom (K : CochainComplex.Plus C')
    [IsIso ((mapCochainComplexPlusDerivedUnit Φ).app K)] :
    twistComparison F₁' F₂ K ≫ (acyclicTwistTransportIso F₁ F₂ Φ F₁' κ K).hom =
      DerivedCategory.Plus.Q.map (F₂.mapCochainComplexPlus.map
          (ObjectProperty.homMk ((NatTrans.mapHomologicalComplex κ.inv _).app K.obj) :
            F₁'.mapCochainComplexPlus.obj K ⟶
              F₁.mapCochainComplexPlus.obj (Φ.mapCochainComplexPlus.obj K))) ≫
        twistComparison F₁ F₂ (Φ.mapCochainComplexPlus.obj K) := by
  let m : F₁.mapCochainComplexPlus.obj (Φ.mapCochainComplexPlus.obj K) ⟶
      F₁'.mapCochainComplexPlus.obj K :=
    ObjectProperty.homMk ((NatTrans.mapHomologicalComplex κ.hom _).app K.obj)
  let m' : F₁'.mapCochainComplexPlus.obj K ⟶
      F₁.mapCochainComplexPlus.obj (Φ.mapCochainComplexPlus.obj K) :=
    ObjectProperty.homMk ((NatTrans.mapHomologicalComplex κ.inv _).app K.obj)
  have hmm : m' ≫ m = 𝟙 _ := by
    ext n : 2
    exact κ.inv_hom_id_app (K.obj.X n)
  have h := mapCochainComplexPlusDerivedUnit_app_comp_map_unit_acyclicTransport F₁ Φ F₁' κ K
  have h' : (mapCochainComplexPlusDerivedUnit F₁').app K ≫
        (Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso Φ F₁ F₁' κ).hom.app
          (DerivedCategory.Plus.Q.obj K) ≫
        F₁.rightDerivedFunctorPlus.map
          (CategoryTheory.inv ((mapCochainComplexPlusDerivedUnit Φ).app K)) =
      DerivedCategory.Plus.Q.map m' ≫
        (mapCochainComplexPlusDerivedUnit F₁).app (Φ.mapCochainComplexPlus.obj K) := by
    rw [← Category.assoc, ← cancel_mono (F₁.rightDerivedFunctorPlus.map
        ((mapCochainComplexPlusDerivedUnit Φ).app K)), Category.assoc, ← Functor.map_comp,
      IsIso.inv_hom_id, Functor.map_id]
    refine (Category.comp_id _).trans ?_
    rw [Category.assoc, h, ← Category.assoc, ← Functor.map_comp, hmm, Functor.map_id]
    exact (Category.id_comp _).symm
  have hn := (mapCochainComplexPlusDerivedUnit F₂).naturality m'
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [twistComparison, acyclicTwistTransportIso, Functor.mapIso_hom, Iso.trans_hom,
    Iso.app_hom, Iso.symm_hom, asIso_inv, Category.assoc, ← Functor.map_comp]
  rw [h', Functor.map_comp, ← Category.assoc, ← hn, Category.assoc]

/-- **The transport isomorphism against the resolution comparisons.** For a quasi-isomorphism
`ψ : K ⟶ T` into a bounded below complex of injectives, the transport isomorphism is read on the
injective resolutions `T` and `Φ(T)` off the componentwise `κ⁻¹`. -/
lemma acyclicTwistTransportIso_hom_comp_twistResolutionIso {K T : CochainComplex.Plus C'}
    (ψ : K ⟶ T) [QuasiIso ψ.hom] (hT : ∀ n, Injective (T.obj.X n))
    [IsIso ((mapCochainComplexPlusDerivedUnit Φ).app K)] [F₁'.PreservesInjectiveObjects]
    [QuasiIso (Φ.mapCochainComplexPlus.map ψ).hom]
    (hΦT : ∀ n, Injective ((Φ.mapCochainComplexPlus.obj T).obj.X n)) :
    DerivedCategory.Plus.ι.map (acyclicTwistTransportIso F₁ F₂ Φ F₁' κ K).hom ≫
        (twistResolutionIso F₁ F₂ (Φ.mapCochainComplexPlus.map ψ) hΦT).hom =
      (twistResolutionIso F₁' F₂ ψ hT).hom ≫
        DerivedCategory.Q.map (F₂.mapCochainComplexPlus.map
          (ObjectProperty.homMk ((NatTrans.mapHomologicalComplex κ.inv _).app T.obj) :
            F₁'.mapCochainComplexPlus.obj T ⟶
              F₁.mapCochainComplexPlus.obj (Φ.mapCochainComplexPlus.obj T))).hom := by
  have := isIso_mapCochainComplexPlusDerivedUnit_app_of_injective Φ T hT
  have := isIso_twistComparison F₁ F₂ (Φ.mapCochainComplexPlus.obj T) hΦT
  have := isIso_twistComparison F₁' F₂ T hT
  let mT : F₁'.mapCochainComplexPlus.obj T ⟶
      F₁.mapCochainComplexPlus.obj (Φ.mapCochainComplexPlus.obj T) :=
    ObjectProperty.homMk ((NatTrans.mapHomologicalComplex κ.inv _).app T.obj)
  have hn := acyclicTwistTransportIso_hom_naturality F₁ F₂ Φ F₁' κ ψ
  have hc := twistComparison_comp_acyclicTwistTransportIso_hom F₁ F₂ Φ F₁' κ T
  have hc' : (acyclicTwistTransportIso F₁ F₂ Φ F₁' κ T).hom ≫
      CategoryTheory.inv (twistComparison F₁ F₂ (Φ.mapCochainComplexPlus.obj T)) =
      CategoryTheory.inv (twistComparison F₁' F₂ T) ≫
        DerivedCategory.Plus.Q.map (F₂.mapCochainComplexPlus.map mT) := by
    exact comp_inv_eq_inv_comp_of_comp_eq hc
  show DerivedCategory.Plus.ι.map _ ≫ DerivedCategory.Plus.ι.map _ =
    DerivedCategory.Plus.ι.map _ ≫ DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.Q.map (F₂.mapCochainComplexPlus.map mT))
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  show (acyclicTwistTransportIso F₁ F₂ Φ F₁' κ K).hom ≫ (F₂.rightDerivedFunctorPlus.map
      (F₁.rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map (Φ.mapCochainComplexPlus.map ψ))) ≫
        CategoryTheory.inv (twistComparison F₁ F₂ (Φ.mapCochainComplexPlus.obj T))) =
    (F₂.rightDerivedFunctorPlus.map
      (F₁'.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map ψ)) ≫
        CategoryTheory.inv (twistComparison F₁' F₂ T)) ≫
      DerivedCategory.Plus.Q.map (F₂.mapCochainComplexPlus.map mT)
  rw [← Category.assoc, ← hn, Category.assoc, hc', Category.assoc]

variable (P' : C' ⥤ C') [P'.Additive] [P'.PreservesInjectiveObjects] (θ : P ⋙ F₁ ≅ F₁)
  (θ' : P' ⋙ F₁' ≅ F₁') (ρ : P' ⋙ Φ ≅ Φ ⋙ P)

omit [EnoughInjectives C] [EnoughInjectives D] [P.PreservesInjectiveObjects]
  [F₁.PreservesInjectiveObjects] [EnoughInjectives C'] [Φ.PreservesInjectiveObjects]
  [P'.PreservesInjectiveObjects] in
/-- **Chain-level intertwining.** For a twist `g'` of `T`, the componentwise `κ⁻¹` intertwines
the chain endomorphism induced by `g'` with the one induced by the twist `Φ(g') ≫ ρ` of `Φ(T)`. -/
lemma twistChainEndo_comp_map_acyclicTransport
    (hρ : ∀ X : C', F₁.map (ρ.hom.app X) ≫ θ.hom.app (Φ.obj X) ≫ κ.hom.app X =
      κ.hom.app (P'.obj X) ≫ θ'.hom.app X)
    (T : CochainComplex.Plus C') (g' : T ⟶ P'.mapCochainComplexPlus.obj T) :
    twistChainEndo P' F₁' F₂ θ' T g' ≫ F₂.mapCochainComplexPlus.map
        (ObjectProperty.homMk ((NatTrans.mapHomologicalComplex κ.inv _).app T.obj) :
          F₁'.mapCochainComplexPlus.obj T ⟶
            F₁.mapCochainComplexPlus.obj (Φ.mapCochainComplexPlus.obj T)) =
      F₂.mapCochainComplexPlus.map
          (ObjectProperty.homMk ((NatTrans.mapHomologicalComplex κ.inv _).app T.obj) :
            F₁'.mapCochainComplexPlus.obj T ⟶
              F₁.mapCochainComplexPlus.obj (Φ.mapCochainComplexPlus.obj T)) ≫
        twistChainEndo P F₁ F₂ θ (Φ.mapCochainComplexPlus.obj T)
          (Φ.mapCochainComplexPlus.map g' ≫
            (ObjectProperty.homMk ((NatTrans.mapHomologicalComplex ρ.hom _).app T.obj) :
              Φ.mapCochainComplexPlus.obj (P'.mapCochainComplexPlus.obj T) ⟶
                P.mapCochainComplexPlus.obj (Φ.mapCochainComplexPlus.obj T))) := by
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
  have sq2 : ∀ {A : Type _} [Category A] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : A}
      (x : X₀ ⟶ X₁) (t' : X₁ ⟶ X₂) (ki : X₂ ⟶ X₃) (kiP : X₁ ⟶ X₄) (ki₀ : X₀ ⟶ X₅)
      (y : X₅ ⟶ X₄) (r : X₄ ⟶ X₆) (t : X₆ ⟶ X₃), x ≫ kiP = ki₀ ≫ y →
      t' ≫ ki = kiP ≫ r ≫ t → (x ≫ t') ≫ ki = ki₀ ≫ (y ≫ r) ≫ t := by
    intro A _ X₀ X₁ X₂ X₃ X₄ X₅ X₆ x t' ki kiP ki₀ y r t hκ hρ
    rw [Category.assoc, hρ, reassoc_of% hκ, Category.assoc]
  exact (sq2 _ _ _ _ _ _ _ _ hκ hρ').trans
    (congrArg (fun z => κ.inv.app (T.obj.X n) ≫ z ≫ θ.hom.app (Φ.obj (T.obj.X n)))
      (F₁.map_comp _ _).symm)

/-- **Transport of a twisted endomorphism along a functor acyclic on the complex.** Let
`Φ : 𝒞' ⥤ 𝒞` be additive and preserve injective objects, with `κ : Φ ⋙ F₁ ≅ F₁'` and
`ρ : P' ⋙ Φ ≅ Φ ⋙ P` compatible with `θ` and `θ'`, and let `K` be a complex at which the unit
`Φ(K) ⟶ RΦ(K)` is invertible. For a twist `τ'` of `K`, the transport isomorphism intertwines
the endomorphism induced by `τ'` with the endomorphism induced by the twist `Φ(τ') ≫ ρ` of
`Φ(K)`. -/
theorem derivedTwistEndo_acyclicTransport
    (hρ : ∀ X : C', F₁.map (ρ.hom.app X) ≫ θ.hom.app (Φ.obj X) ≫ κ.hom.app X =
      κ.hom.app (P'.obj X) ≫ θ'.hom.app X)
    (K : CochainComplex.Plus C') [IsIso ((mapCochainComplexPlusDerivedUnit Φ).app K)]
    (τ' : K ⟶ P'.mapCochainComplexPlus.obj K) :
    derivedTwistEndo P' F₁' F₂ θ' K τ' ≫ (acyclicTwistTransportIso F₁ F₂ Φ F₁' κ K).hom =
      (acyclicTwistTransportIso F₁ F₂ Φ F₁' κ K).hom ≫ derivedTwistEndo P F₁ F₂ θ
        (Φ.mapCochainComplexPlus.obj K)
        (Φ.mapCochainComplexPlus.map τ' ≫
          (ObjectProperty.homMk ((NatTrans.mapHomologicalComplex ρ.hom _).app K.obj) :
            Φ.mapCochainComplexPlus.obj (P'.mapCochainComplexPlus.obj K) ⟶
              P.mapCochainComplexPlus.obj (Φ.mapCochainComplexPlus.obj K))) := by
  have := preservesInjectiveObjects_of_comp_iso κ
  let tw : ∀ L : CochainComplex.Plus C', Φ.mapCochainComplexPlus.obj
      (P'.mapCochainComplexPlus.obj L) ⟶
        P.mapCochainComplexPlus.obj (Φ.mapCochainComplexPlus.obj L) :=
    fun L => ObjectProperty.homMk ((NatTrans.mapHomologicalComplex ρ.hom _).app L.obj)
  obtain ⟨a, ha⟩ := K.property
  have : K.obj.IsStrictlyGE a := ha
  obtain ⟨R, -, -⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE a K.obj
  let T : CochainComplex.Plus C' := ⟨R.cocomplex, R.boundedBelow⟩
  let ψ : K ⟶ T := ObjectProperty.homMk R.ι
  have : QuasiIso ψ.hom := R.quasiIso
  have hT : ∀ n, Injective (T.obj.X n) := R.injective
  have := isIso_mapCochainComplexPlusDerivedUnit_app_of_injective Φ T hT
  have := quasiIso_mapCochainComplexPlus_map_of_isIso_derivedUnit Φ ψ
  have hΦT : ∀ n, Injective ((Φ.mapCochainComplexPlus.obj T).obj.X n) := fun n =>
    Φ.injective_obj_of_injective (hT n)
  have : ∀ n, Injective ((P'.mapCochainComplexPlus.obj T).obj.X n) := fun n =>
    P'.injective_obj_of_injective (hT n)
  obtain ⟨g', hg'⟩ := exists_twist_lift P' ψ hT τ'
  let g := Φ.mapCochainComplexPlus.map g' ≫ tw T
  have hnat : tw K ≫ P.mapCochainComplexPlus.map (Φ.mapCochainComplexPlus.map ψ) =
        Φ.mapCochainComplexPlus.map (P'.mapCochainComplexPlus.map ψ) ≫ tw T := by
    ext n : 2
    exact (ρ.hom.naturality (ψ.hom.f n)).symm
  have h₁ : DerivedCategory.Plus.Q.map (Φ.mapCochainComplexPlus.map
        (τ' ≫ P'.mapCochainComplexPlus.map ψ)) =
      DerivedCategory.Plus.Q.map (Φ.mapCochainComplexPlus.map (ψ ≫ g')) :=
    DerivedCategory.Plus.ι.map_injective
      (Q_map_mapHomologicalComplex_eq_of_injective Φ (P'.mapCochainComplexPlus.obj T).property
        (congrArg DerivedCategory.Plus.ι.map hg'))
  have hg : DerivedCategory.Plus.Q.map ((Φ.mapCochainComplexPlus.map τ' ≫ tw K) ≫
        P.mapCochainComplexPlus.map (Φ.mapCochainComplexPlus.map ψ)) =
      DerivedCategory.Plus.Q.map (Φ.mapCochainComplexPlus.map ψ ≫ g) := by
    rw [Category.assoc, hnat, ← Category.assoc, ← Functor.map_comp, Functor.map_comp,
      h₁, ← Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp,
      Functor.map_comp, Category.assoc]
    show _ = _ ≫ DerivedCategory.Plus.Q.map (Φ.mapCochainComplexPlus.map g' ≫ tw T)
    rw [Functor.map_comp]
  have e₁ := twistResolutionIso_hom_comp P' F₁' F₂ θ' ψ hT τ' g' hg'
  have e₂ := twistResolutionIso_hom_comp P F₁ F₂ θ (Φ.mapCochainComplexPlus.map ψ) hΦT _ g hg
  have e₃ := acyclicTwistTransportIso_hom_comp_twistResolutionIso F₁ F₂ Φ F₁' κ ψ hT hΦT
  have := isIso_twistComparison F₁ F₂ (Φ.mapCochainComplexPlus.obj T) hΦT
  refine DerivedCategory.Plus.ι.map_injective ?_
  rw [Functor.map_comp, Functor.map_comp, ← cancel_mono
    (twistResolutionIso F₁ F₂ (Φ.mapCochainComplexPlus.map ψ) hΦT).hom, Category.assoc,
    Category.assoc, e₂, reassoc_of% e₃, e₃, reassoc_of% e₁]
  congr 1
  rw [← Functor.map_comp, ← Functor.map_comp, ← ObjectProperty.FullSubcategory.comp_hom,
    ← ObjectProperty.FullSubcategory.comp_hom,
    twistChainEndo_comp_map_acyclicTransport P F₁ F₂ Φ F₁' κ P' θ θ' ρ hρ]

end CategoryTheory.Functor

end
