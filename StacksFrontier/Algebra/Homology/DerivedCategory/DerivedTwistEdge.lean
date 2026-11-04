module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ShortExactDerivedTrace
public import StacksFrontier.Homology.DerivedIndexing.Composite
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit

/-!
# The derived endomorphism attached to a twist, read through the edge morphism

Let `P : 𝒞 ⥤ 𝒞`, `F₁ : 𝒞 ⥤ 𝒟` and `F₂ : 𝒟 ⥤ ℰ` be additive functors with `P` and `F₁`
preserving injective objects, let `θ : P ⋙ F₁ ≅ F₁`, and let `e : F₁ ⋙ F₂ ≅ H`. A twist
`τ : K ⟶ P(K)` of a bounded below complex induces the endomorphism
`CategoryTheory.Functor.derivedTwistEndo P F₁ F₂ θ K τ` of `RF₂(RF₁(K))`: `RF₂ ∘ RF₁` of
`K ⟶ P(K) ⟶ RP(K)` followed by the comparison `RF₁ ∘ RP ≅ RF₁` attached to `θ`. For `P = π̄_*`,
`F₁ = f_*` and `F₂ = Γ(Spec k̄, -)` this is the canonical geometric Frobenius on
`RΓ_c(X_k̄, K)` of the trace formula.

This file moves that endomorphism to `RH` along `RH ≅ RF₁ ⋙ RF₂` and identifies what is left
once the twist has been applied: the comparison `RF₂ ∘ RF₁ ∘ RP ≅ RF₂ ∘ RF₁` attached to `θ`
becomes, on `RH`, the composition comparison `RH ∘ RP ≅ R(P ⋙ H)` of [Stacks, Tag 015M]
followed by the map induced by `θ' : P ⋙ H ≅ H` (`compIsoOfIso_hom_comp_map_inv_comp_inv`). For
an object placed in degree zero and on cohomology, this says that the endomorphism is `τ` on
`RⁱH` followed by the degreewise comparison
`Stacks.DerivedIndexing.rightDerivedPlusEdge P H i : RⁱH ∘ P ⟶ Rⁱ(P ⋙ H)` and the map induced by
`θ'` (`homologyMap_derivedTwistEndo_single`).

## Main results

* `CategoryTheory.Functor.rightDerivedFunctorPlus_natTrans_ext`: a transformation out of a right
  derived functor on `D⁺` is determined by its composites with the derived-functor unit on
  bounded below complexes.
* `CategoryTheory.Functor.compIsoOfIso_hom_comp_map_inv_comp_inv`: **the comparison attached to
  `θ`, transported to `RH`, is the composition comparison followed by the map induced by `θ'`.**
* `CategoryTheory.Functor.homologyMap_derivedTwistEndo_single`: the degreewise form, for an object
  placed in degree zero.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 03UI](https://stacks.math.columbia.edu/tag/03UI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁

namespace CategoryTheory.Functor

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section Ext

/-- Conjugating a component of a natural transformation by an isomorphism, abstract in the
objects. -/
private lemma nat_conj {A B : Type*} [Category* A] [Category* B] {F' G' : A ⥤ B} {X Y : A}
    {Z : B} (j : X ≅ Y) (γ : F' ⟶ G') (u : Z ⟶ F'.obj X) :
    u ≫ γ.app X = (u ≫ F'.map j.hom) ≫ γ.app Y ≫ G'.map j.inv := by
  simp

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D] [EnoughInjectives C]

/-- **A transformation out of a right derived functor on `D⁺` is determined by its composites with
the derived-functor unit on bounded below complexes.** This is the universal property of the
right derived functor, read through the localization of bounded below complexes. -/
theorem rightDerivedFunctorPlus_natTrans_ext (F : C ⥤ D) [F.Additive]
    {G : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D} (α β : F.rightDerivedFunctorPlus ⟶ G)
    (h : ∀ K : CochainComplex.Plus C, (mapCochainComplexPlusDerivedUnit F).app K ≫
      α.app (DerivedCategory.Plus.Q.obj K) =
        (mapCochainComplexPlusDerivedUnit F).app K ≫ β.app (DerivedCategory.Plus.Q.obj K)) :
    α = β := by
  refine Functor.rightDerived_ext _ F.rightDerivedFunctorPlusUnit
    (HomotopyCategory.Plus.quasiIso C) _ α β (NatTrans.ext (funext fun L => ?_))
  obtain ⟨K, rfl⟩ := HomotopyCategory.Plus.quotient_obj_surjective L
  have key : ∀ γ : F.rightDerivedFunctorPlus ⟶ G,
      F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient C).obj K) ≫
          γ.app (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj K)) =
        (DerivedCategory.Plus.quotientCompQhIso D).hom.app (F.mapCochainComplexPlus.obj K) ≫
          ((mapCochainComplexPlusDerivedUnit F).app K ≫ γ.app (DerivedCategory.Plus.Q.obj K)) ≫
            G.map ((DerivedCategory.Plus.quotientCompQhIso C).inv.app K) := by
    intro γ
    simp only [mapCochainComplexPlusDerivedUnit_app, Category.assoc, Iso.hom_inv_id_app_assoc]
    exact nat_conj _ γ _
  show F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient C).obj K) ≫
      α.app (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj K)) =
    F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient C).obj K) ≫
      β.app (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj K))
  rw [key α, key β, h K]

/-- **The derived-functor unit against the map of right derived functors induced by a natural
transformation.** For `τ : F₁ ⟶ F₂`, the unit of `RF₁` at a bounded below complex `K` followed by
the induced map `RF₁ ⟶ RF₂` is `τ` applied degreewise followed by the unit of `RF₂`. -/
theorem mapCochainComplexPlusDerivedUnit_app_comp_rightDerivedFunctorPlusNatTrans
    {F₁ F₂ : C ⥤ D} [F₁.Additive] [F₂.Additive] (τ : F₁ ⟶ F₂) (K : CochainComplex.Plus C) :
    (mapCochainComplexPlusDerivedUnit F₁).app K ≫
        (Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans τ).app
          (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map
          (ObjectProperty.homMk ((NatTrans.mapHomologicalComplex τ _).app K.obj) :
            F₁.mapCochainComplexPlus.obj K ⟶ F₂.mapCochainComplexPlus.obj K) ≫
        (mapCochainComplexPlusDerivedUnit F₂).app K := by
  have hn := (Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans τ).naturality
    ((DerivedCategory.Plus.quotientCompQhIso C).hom.app K)
  have hq := (DerivedCategory.Plus.quotientCompQhIso D).inv.naturality
    (ObjectProperty.homMk ((NatTrans.mapHomologicalComplex τ _).app K.obj) :
      F₁.mapCochainComplexPlus.obj K ⟶ F₂.mapCochainComplexPlus.obj K)
  have hfac := Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans_app τ
    ((HomotopyCategory.Plus.quotient C).obj K)
  have hmap : (Functor.mapHomotopyCategoryPlusNatTrans τ).app
      ((HomotopyCategory.Plus.quotient C).obj K) =
      (HomotopyCategory.Plus.quotient D).map
        (ObjectProperty.homMk ((NatTrans.mapHomologicalComplex τ _).app K.obj) :
          F₁.mapCochainComplexPlus.obj K ⟶ F₂.mapCochainComplexPlus.obj K) := by
    ext
    rfl
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn hq
  rw [hmap] at hfac
  rw [mapCochainComplexPlusDerivedUnit_app, mapCochainComplexPlusDerivedUnit_app]
  exact comp_eq_of_three_squares _ _ _ _ _ _ _ _ _ _ hn hfac hq

end Ext

section CompIso

/-- The algebra behind `mapCochainComplexPlusDerivedUnit_app_comp_compIsoOfIso_hom`, abstract in
the objects. -/
private lemma unit_conj_aux {A : Type*} [Category* A] {X₀ X₁ X₂ Y₀ Z : A}
    {u' : X₀ ⟶ X₁} {ih : X₁ ⟶ X₂} {q : X₀ ⟶ Y₀} {v : Y₀ ⟶ X₂} {t : X₁ ⟶ Z} {w : X₀ ⟶ Z}
    {ii : X₂ ⟶ X₁} {q' : Y₀ ⟶ X₀}
    (h1 : u' ≫ ih = q ≫ v) (h2 : u' ≫ t = w) (hqq : q' ≫ q = 𝟙 Y₀) (hinv : ih ≫ ii = 𝟙 X₁) :
    v ≫ ii ≫ t = q' ≫ w := by
  rw [← h2, ← Category.id_comp v, ← hqq]
  simp only [Category.assoc]
  rw [← reassoc_of% h1, reassoc_of% hinv]

/-- The degreewise inverse isomorphisms of a natural isomorphism give inverse maps in `D⁺`. -/
private lemma Q_map_homMk_inv_comp_hom {C D : Type*} [Category* C] [Category* D] [Abelian C]
    [Abelian D] [EnoughInjectives C] {F' G' : C ⥤ D} [F'.Additive] [G'.Additive] (e : F' ≅ G')
    (K : CochainComplex.Plus C) :
    DerivedCategory.Plus.Q.map
        (ObjectProperty.homMk ((NatTrans.mapHomologicalComplex e.inv _).app K.obj) :
          G'.mapCochainComplexPlus.obj K ⟶ F'.mapCochainComplexPlus.obj K) ≫
      DerivedCategory.Plus.Q.map
        (ObjectProperty.homMk ((NatTrans.mapHomologicalComplex e.hom _).app K.obj) :
          F'.mapCochainComplexPlus.obj K ⟶ G'.mapCochainComplexPlus.obj K) = 𝟙 _ := by
  refine (DerivedCategory.Plus.Q.map_comp _ _).symm.trans ?_
  refine Eq.trans (congrArg DerivedCategory.Plus.Q.map ?_) (DerivedCategory.Plus.Q.map_id _)
  ext n : 2
  exact e.inv_hom_id_app ((K.obj).X n)

variable {C D E : Type u₁} [Category.{v₁} C] [Category.{v₁} D] [Category.{v₁} E] [Abelian C]
  [Abelian D]
  [Abelian E] [EnoughInjectives C] [EnoughInjectives D]

/-- **The derived-functor unit against the comparison `RH ≅ RF ⋙ RG` attached to `F ⋙ G ≅ H`.**
The unit of `RH` at a bounded below complex `K` followed by the comparison is `e⁻¹` applied
degreewise, then the unit of `RG` at `F(K)` and `RG` of the unit of `RF` at `K`. -/
theorem mapCochainComplexPlusDerivedUnit_app_comp_compIsoOfIso_hom (F : C ⥤ D) (G : D ⥤ E)
    (H : C ⥤ E) [F.Additive] [G.Additive] [H.Additive] [F.PreservesInjectiveObjects]
    (e : F ⋙ G ≅ H) (K : CochainComplex.Plus C) :
    (mapCochainComplexPlusDerivedUnit H).app K ≫
        (Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso F G H e).hom.app
          (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map
          (ObjectProperty.homMk ((NatTrans.mapHomologicalComplex e.inv _).app K.obj) :
            H.mapCochainComplexPlus.obj K ⟶ (F ⋙ G).mapCochainComplexPlus.obj K) ≫
        (mapCochainComplexPlusDerivedUnit G).app (F.mapCochainComplexPlus.obj K) ≫
          G.rightDerivedFunctorPlus.map ((mapCochainComplexPlusDerivedUnit F).app K) := by
  have h1 := mapCochainComplexPlusDerivedUnit_app_comp_rightDerivedFunctorPlusIsoOfCompIso_hom
    F G H e K
  have h2 := mapCochainComplexPlusDerivedUnit_comp F G (rightDerivedFunctorPlusComp F G)
    (rightDerivedFunctorPlusComp_fac F G) K
  show (mapCochainComplexPlusDerivedUnit H).app K ≫
      (Stacks.EtaleCohomology.rightDerivedFunctorPlusIsoOfCompIso F G H e).inv.app
          (DerivedCategory.Plus.Q.obj K) ≫
        (rightDerivedFunctorPlusComp F G).app (DerivedCategory.Plus.Q.obj K) = _
  refine unit_conj_aux h1 h2 ?_
    ((Stacks.EtaleCohomology.rightDerivedFunctorPlusIsoOfCompIso F G H e).hom_inv_id_app _)
  exact Q_map_homMk_inv_comp_hom e K

/-- The algebra behind `compIsoOfIso_hom_comp_map_inv_comp_inv`: pasting six squares, abstract in
the objects. -/
private lemma chase_aux {A : Type*} [Category* A]
    {X0 X1 X2 X3 X4 X5 A1 A2 B0 B1 B2 C0 D0 : A}
    {u : X0 ⟶ X1} {t : X1 ⟶ X2} {ch' : X2 ⟶ X3} {r : X3 ⟶ X4} {ci : X4 ⟶ X5}
    {a : X0 ⟶ A1} {m : A1 ⟶ X2} (h1 : u ≫ t = a ≫ m)
    {ch : A1 ⟶ A2} {mm : A2 ⟶ X3} (h2 : m ≫ ch' = ch ≫ mm)
    {q1 : X0 ⟶ B0} {b : B0 ⟶ B1} {y : B1 ⟶ A2} (h3 : a ≫ ch = q1 ≫ b ≫ y)
    {z : B1 ⟶ B2} {wf : B2 ⟶ X4} (h4 : y ≫ mm ≫ r = z ≫ wf)
    {q2 : B0 ⟶ C0} {b' : C0 ⟶ B2} (h5 : b ≫ z = q2 ≫ b')
    {q3 : C0 ⟶ D0} {v : D0 ⟶ X5} (hcv : b' ≫ wf ≫ ci = q3 ≫ v)
    {q : X0 ⟶ D0} (hq : q1 ≫ q2 ≫ q3 = q) :
    u ≫ t ≫ ch' ≫ r ≫ ci = q ≫ v := by
  rw [reassoc_of% h1, reassoc_of% h2, reassoc_of% h3, reassoc_of% h4, reassoc_of% h5, hcv,
    ← hq]
  simp only [Category.assoc]

/-- Inverting the comparison in a unit square, abstract in the objects. -/
private lemma unit_inv_aux {A : Type*} [Category* A] {Y0 Y1 Y2 Z0 : A}
    {v : Y0 ⟶ Y1} {ch : Y1 ⟶ Y2} {ci : Y2 ⟶ Y1} {qi : Y0 ⟶ Z0} {bw : Z0 ⟶ Y2} {qh : Z0 ⟶ Y0}
    (h : v ≫ ch = qi ≫ bw) (hc : ch ≫ ci = 𝟙 Y1) (hq : qh ≫ qi = 𝟙 Z0) :
    bw ≫ ci = qh ≫ v := by
  rw [← Category.id_comp bw, ← hq]
  simp only [Category.assoc]
  rw [← reassoc_of% h, hc, Category.comp_id]

/-- Moving an isomorphism across an equation, abstract in the objects. -/
private lemma comp_inv_of_eq_aux {A : Type*} [Category* A] {X Y Z W : A} {x : X ⟶ Y}
    {y : Y ⟶ Z} (c : W ≅ Z) {z : X ⟶ W} (h : x ≫ y = z ≫ c.hom) : x ≫ y ≫ c.inv = z := by
  rw [← Category.assoc, h]
  simp

/-- A functor carries a composite of three morphisms to the composite of their images, abstract in
the objects. -/
private lemma map_comp₃_aux {A B : Type*} [Category* A] [Category* B] (G : A ⥤ B) {W X Y Z : A}
    {a : W ⟶ X} {b : X ⟶ Y} {c : Y ⟶ Z} {d : W ⟶ Z} (h : a ≫ b ≫ c = d) :
    G.map a ≫ G.map b ≫ G.map c = G.map d := by
  rw [← h, G.map_comp, G.map_comp]

end CompIso

section Twist

variable {C D E : Type u₁} [Category.{v₁} C] [Category.{v₁} D] [Category.{v₁} E] [Abelian C]
  [Abelian D] [Abelian E] [EnoughInjectives C] [EnoughInjectives D]
  (P : C ⥤ C) (F₁ : C ⥤ D) (F₂ : D ⥤ E) (H : C ⥤ E) [P.Additive] [F₁.Additive] [F₂.Additive]
  [H.Additive] [P.PreservesInjectiveObjects] [F₁.PreservesInjectiveObjects]
  (θ : P ⋙ F₁ ≅ F₁) (e : F₁ ⋙ F₂ ≅ H)

/-- The isomorphism `P ⋙ H ≅ H` induced by `θ : P ⋙ F₁ ≅ F₁` through `e : F₁ ⋙ F₂ ≅ H`. -/
def twistEdgeIso : P ⋙ H ≅ H :=
  Functor.isoWhiskerLeft P e.symm ≪≫ (Functor.associator P F₁ F₂).symm ≪≫
    Functor.isoWhiskerRight θ F₂ ≪≫ e

omit [Abelian C] [Abelian D] [Abelian E] [EnoughInjectives C] [EnoughInjectives D] [P.Additive]
  [F₁.Additive] [F₂.Additive] [H.Additive] [P.PreservesInjectiveObjects]
  [F₁.PreservesInjectiveObjects] in
/-- The component of `twistEdgeIso P F₁ F₂ H θ e` at `X` is
`e.inv.app (P.obj X) ≫ F₂.map (θ.hom.app X) ≫ e.hom.app X`. -/
@[simp]
lemma twistEdgeIso_hom_app (X : C) :
    (twistEdgeIso P F₁ F₂ H θ e).hom.app X =
      e.inv.app (P.obj X) ≫ F₂.map (θ.hom.app X) ≫ e.hom.app X := by
  simp [twistEdgeIso]

/-- **The comparison attached to `θ`, moved to `RH`.** Transporting the comparison
`RF₂ ∘ RF₁ ∘ RP ≅ RF₂ ∘ RF₁` attached to `θ` along `RH ≅ RF₁ ⋙ RF₂` gives the inverse of the
composition comparison `R(P ⋙ H) ≅ RP ⋙ RH` of [Stacks, Tag 015M] followed by the map
`R(P ⋙ H) ⟶ RH` induced by `θ' : P ⋙ H ≅ H`. -/
theorem compIsoOfIso_hom_comp_map_inv_comp_inv (K : DerivedCategory.Plus C) :
    (Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso F₁ F₂ H e).hom.app
        (P.rightDerivedFunctorPlus.obj K) ≫
      F₂.rightDerivedFunctorPlus.map
        ((Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso P F₁ F₁ θ).inv.app K) ≫
      (Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso F₁ F₂ H e).inv.app K =
    (Stacks.DerivedIndexing.rightDerivedPlusCompIso P H).inv.app K ≫
      (Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans
        (twistEdgeIso P F₁ F₂ H θ e).hom).app K := by
  let c₁ := Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso F₁ F₂ H e
  let c₂ := Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso P F₁ F₁ θ
  let L : P.rightDerivedFunctorPlus ⋙ H.rightDerivedFunctorPlus ⟶ H.rightDerivedFunctorPlus :=
    Functor.whiskerLeft P.rightDerivedFunctorPlus c₁.hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight c₂.inv F₂.rightDerivedFunctorPlus ≫ c₁.inv
  have key : Stacks.DerivedIndexing.rightDerivedPlusCompTrans P H ≫ L =
      Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans (twistEdgeIso P F₁ F₂ H θ e).hom := by
    refine rightDerivedFunctorPlus_natTrans_ext (P ⋙ H) _ _ (fun Kc => ?_)
    have h1 := mapCochainComplexPlusDerivedUnit_comp P H
      (Stacks.DerivedIndexing.rightDerivedPlusCompTrans P H)
      (Stacks.DerivedIndexing.rightDerivedPlusCompTrans_fac P H) Kc
    have h2 := c₁.hom.naturality ((mapCochainComplexPlusDerivedUnit P).app Kc)
    have h3 := mapCochainComplexPlusDerivedUnit_app_comp_compIsoOfIso_hom F₁ F₂ H e
      (P.mapCochainComplexPlus.obj Kc)
    have h4' := mapCochainComplexPlusDerivedUnit_app_comp_map_unit P F₁ θ Kc
    have h4'' : (mapCochainComplexPlusDerivedUnit F₁).app (P.mapCochainComplexPlus.obj Kc) ≫
        F₁.rightDerivedFunctorPlus.map ((mapCochainComplexPlusDerivedUnit P).app Kc) ≫
          c₂.inv.app (DerivedCategory.Plus.Q.obj Kc) =
        DerivedCategory.Plus.Q.map (twistCompMap P F₁ θ Kc) ≫
          (mapCochainComplexPlusDerivedUnit F₁).app Kc :=
      comp_inv_of_eq_aux (c₂.app (DerivedCategory.Plus.Q.obj Kc))
        (h4'.trans (Category.assoc _ _ _).symm)
    have h4 := congrArg F₂.rightDerivedFunctorPlus.map h4''
    simp only [Functor.map_comp] at h4
    have h5 := (mapCochainComplexPlusDerivedUnit F₂).naturality (twistCompMap P F₁ θ Kc)
    have h6 := mapCochainComplexPlusDerivedUnit_app_comp_compIsoOfIso_hom F₁ F₂ H e Kc
    have hcv := unit_inv_aux h6 (c₁.hom_inv_id_app (DerivedCategory.Plus.Q.obj Kc))
      (qh := DerivedCategory.Plus.Q.map
        (ObjectProperty.homMk ((NatTrans.mapHomologicalComplex e.hom _).app Kc.obj) :
          (F₁ ⋙ F₂).mapCochainComplexPlus.obj Kc ⟶ H.mapCochainComplexPlus.obj Kc))
      (Q_map_homMk_inv_comp_hom e.symm Kc)
    have hR := mapCochainComplexPlusDerivedUnit_app_comp_rightDerivedFunctorPlusNatTrans
      (twistEdgeIso P F₁ F₂ H θ e).hom Kc
    have hL : (Stacks.DerivedIndexing.rightDerivedPlusCompTrans P H ≫ L).app
        (DerivedCategory.Plus.Q.obj Kc) =
        (Stacks.DerivedIndexing.rightDerivedPlusCompTrans P H).app (DerivedCategory.Plus.Q.obj Kc) ≫
          c₁.hom.app (P.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj Kc)) ≫
          F₂.rightDerivedFunctorPlus.map (c₂.inv.app (DerivedCategory.Plus.Q.obj Kc)) ≫
          c₁.inv.app (DerivedCategory.Plus.Q.obj Kc) := by
      simp [L]
    rw [hR, hL]
    refine chase_aux h1 h2 h3 h4 h5.symm ((Category.assoc _ _ _).symm.trans hcv) ?_
    refine map_comp₃_aux DerivedCategory.Plus.Q ?_
    ext n : 2
    exact (twistEdgeIso_hom_app P F₁ F₂ H θ e (Kc.obj.X n)).symm
  have hK := NatTrans.congr_app key K
  simp only [NatTrans.comp_app] at hK
  rw [← hK]
  simp [L, Stacks.DerivedIndexing.rightDerivedPlusCompIso]
  rfl

/-- Pasting a naturality square into a composite, abstract in the objects. -/
private lemma paste_aux {A : Type*} [Category* A] {W X Y Z U V : A} {x : W ⟶ X} {y : X ⟶ Y}
    {z : W ⟶ Z} {a : Z ⟶ Y} {b : Y ⟶ U} {c : U ⟶ V} (h : x ≫ y = z ≫ a) :
    z ≫ (a ≫ b) ≫ c = x ≫ y ≫ b ≫ c := by
  rw [reassoc_of% h, Category.assoc]

/-- Splitting the image of a composite under a composite of functors, abstract in the objects. -/
private lemma map_map_comp_aux {A B B' : Type*} [Category* A] [Category* B] [Category* B']
    (F' : A ⥤ B) (G : B ⥤ B') {W X Y : A} {Z V : B} (a : W ⟶ X) (b : X ⟶ Y)
    (c : F'.obj Y ⟶ Z) (d : Z ⟶ V) :
    G.map (F'.map (a ≫ b)) ≫ G.map c ≫ G.map d =
      G.map (F'.map a) ≫ (G.map (F'.map b) ≫ G.map c) ≫ G.map d := by
  simp

/-- The twist of `M` placed in degree zero attached to `τ : M ⟶ P M`. -/
abbrev singleTwist {M : C} (τ : M ⟶ P.obj M) :
    (Stacks.DerivedIndexing.singlePlusFunctor C 0).obj M ⟶
      P.mapCochainComplexPlus.obj ((Stacks.DerivedIndexing.singlePlusFunctor C 0).obj M) :=
  (Stacks.DerivedIndexing.singlePlusFunctor C 0).map τ ≫
    (Stacks.DerivedIndexing.mapSinglePlus P 0).app M

/-- **The derived twist endomorphism on cohomology, for an object placed in degree zero.** Moved
to `RH` along `RH ≅ RF₁ ⋙ RF₂`, the `i`-th cohomology of the endomorphism of `RF₂(RF₁(M[0]))`
attached to `τ : M ⟶ P M` is `τ` on `RⁱH`, followed by the degreewise comparison
`Stacks.DerivedIndexing.rightDerivedPlusEdge P H i : RⁱH ∘ P ⟶ Rⁱ(P ⋙ H)` and by the map induced
by `θ' : P ⋙ H ≅ H`. -/
theorem homologyMap_derivedTwistEndo_single (M : C) (τ : M ⟶ P.obj M) (i : ℤ) :
    (DerivedCategory.Plus.homologyFunctor E i).map
        ((Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso F₁ F₂ H e).hom.app
            (DerivedCategory.Plus.Q.obj ((Stacks.DerivedIndexing.singlePlusFunctor C 0).obj M)) ≫
          derivedTwistEndo P F₁ F₂ θ ((Stacks.DerivedIndexing.singlePlusFunctor C 0).obj M)
            (singleTwist P τ) ≫
          (Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso F₁ F₂ H e).inv.app
            (DerivedCategory.Plus.Q.obj ((Stacks.DerivedIndexing.singlePlusFunctor C 0).obj M))) =
      (H.rightDerivedPlus i).map τ ≫ (Stacks.DerivedIndexing.rightDerivedPlusEdge P H i).app M ≫
        (Stacks.DerivedIndexing.rightDerivedPlusNatTrans
          (twistEdgeIso P F₁ F₂ H θ e).hom i).app M := by
  let c₁ := Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso F₁ F₂ H e
  let K := (Stacks.DerivedIndexing.singlePlusFunctor C 0).obj M
  let u := DerivedCategory.Plus.Q.map (singleTwist P τ) ≫ (mapCochainComplexPlusDerivedUnit P).app K
  have hnat := c₁.hom.naturality u
  have hmain := compIsoOfIso_hom_comp_map_inv_comp_inv P F₁ F₂ H θ e (DerivedCategory.Plus.Q.obj K)
  have hu : u = (DerivedCategory.Plus.singleFunctor C 0).map τ ≫
      (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle P).app M := by
    rw [← Stacks.DerivedIndexing.singleDerivedUnit_zero, Stacks.DerivedIndexing.singleDerivedUnit]
    simp only [u, singleTwist, Functor.map_comp, Category.assoc]
    rfl
  have hLHS : c₁.hom.app (DerivedCategory.Plus.Q.obj K) ≫
      derivedTwistEndo P F₁ F₂ θ K (singleTwist P τ) ≫ c₁.inv.app (DerivedCategory.Plus.Q.obj K) =
      H.rightDerivedFunctorPlus.map u ≫
        (Stacks.DerivedIndexing.rightDerivedPlusCompIso P H).inv.app
          (DerivedCategory.Plus.Q.obj K) ≫
        (Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans
          (twistEdgeIso P F₁ F₂ H θ e).hom).app (DerivedCategory.Plus.Q.obj K) := by
    rw [← hmain]
    dsimp only [derivedTwistEndo, Functor.comp_map] at hnat ⊢
    rw [Functor.map_comp]
    exact paste_aux hnat
  show (DerivedCategory.Plus.homologyFunctor E i).map
      (c₁.hom.app (DerivedCategory.Plus.Q.obj K) ≫
        derivedTwistEndo P F₁ F₂ θ K (singleTwist P τ) ≫
        c₁.inv.app (DerivedCategory.Plus.Q.obj K)) = _
  rw [hLHS, hu]
  simp only [Functor.map_comp]
  exact map_map_comp_aux _ _ _ _ _ _

end Twist

end CategoryTheory.Functor

end
