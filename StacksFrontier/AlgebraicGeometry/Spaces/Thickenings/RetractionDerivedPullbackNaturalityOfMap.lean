module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RetractionDerivedPullbackNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RetractionStructureSheafNaturality

/-!
# `G2` and `χ` of Stacks 0DLL at the ring map of a linear map `f : V ⟶ W`

The constructions `G2` and `χ` of Stacks 0DLL take a ring map
`g : 𝒪_X[𝒪_X ⊗_k V] ⟶ 𝒪_X[𝒪_X ⊗_k W]` which, read on the site of `X_V`, is the ring map of
`H : X_W ⟶ X_V`. For `H` over `X` and over `Spec k[W] ⟶ Spec k[V]`, the map induced by
`𝒪_X ⊗_k f` is such a ring map, and `G2` and `χ` are specialised to it.

## Main results

* `AlgebraicGeometry.Space.squareZeroStructureSheafIso_naturality`: the ring map induced by
  `𝒪_X ⊗_k f`, read on the site of `X_V`, is the ring map of `H`.
* `AlgebraicGeometry.Space.squareZeroPushforwardNaturalityIsoOfMap`,
  `AlgebraicGeometry.Space.squareZeroPullbackNaturalityIsoOfMap`,
  `AlgebraicGeometry.Space.squareZeroComplexPullbackNaturalityIsoOfMap` and
  `AlgebraicGeometry.Space.squareZeroDerivedPullbackNaturalityOfMap`: `G2a`, `G2`, `G2` on cochain
  complexes and `χ` at the ring map of `f`.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
-/

@[expose] public noncomputable section

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

open CategoryTheory CategoryTheory.Limits Opposite

universe d d' u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Two morphisms into a base-changed chart agree as soon as their cartesian projections to the
chart do. -/
theorem smallBaseChange_obj_hom_ext {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) {U : SmallEtale B S hS X.1}
    {V : SmallEtale B S hS Y.1} (a b : U ⟶ (smallBaseChange B S hS f hf).obj V)
    (h : a.hom.left ≫ hf.snd V.1.hom = b.hom.left ≫ hf.snd V.1.hom) : a = b :=
  ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _
    (hf.hom_ext ((CostructuredArrow.w a.hom).trans (CostructuredArrow.w b.hom).symm) h))

/-- A morphism into a base-changed chart lying over `X`, followed by the cartesian projection,
lies over `f`. -/
theorem representablePullback_snd_comp_hom {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) {T : BigFppfOver B S hS}
    {t : yoneda.obj T ⟶ X.1} {V : SmallEtale B S hS Y.1} (m : T ⟶ hf.pullback V.1.hom)
    (hm : yoneda.map m ≫ hf.fst V.1.hom = t) :
    yoneda.map (m ≫ hf.snd V.1.hom) ≫ V.1.hom = t ≫ f.hom := by
  rw [Functor.map_comp, Category.assoc, ← hf.w V.1.hom, ← Category.assoc, hm]

/-- Four composable morphisms compose to the identity, through two partial composites. -/
theorem comp_four_eq_id_of_eq {C : Type*} [Category* C] {P Q R T Z : C} {a : P ⟶ Q} {c : Q ⟶ R}
    {s₁ : R ⟶ T} {s₂ : T ⟶ Z} {s₃ : Z ⟶ P} {m : Q ⟶ T} {n : Q ⟶ Z} (h₁ : c ≫ s₁ = m)
    (h₂ : m ≫ s₂ = n) (h₃ : a ≫ n ≫ s₃ = 𝟙 P) : (((a ≫ c) ≫ s₁) ≫ s₂) ≫ s₃ = 𝟙 P := by
  rw [← h₃, ← h₂, ← h₁]
  simp only [Category.assoc]

/-- Four composable morphisms compose to the identity, through a commuting square and two
partial composites. -/
theorem id_eq_comp_four_of_eq {C : Type*} [Category* C] {P Q Q' R T Z : C} {a : P ⟶ Q}
    {c : Q ⟶ R} {s₁ : R ⟶ T} {s₂ : T ⟶ Z} {s₃ : Z ⟶ P} {t : Q ⟶ Q'} {k : Q' ⟶ T} {m : Q' ⟶ Z}
    {n : Q' ⟶ P} (h₁ : c ≫ s₁ = t ≫ k) (h₂ : k ≫ s₂ = m) (h₃ : m ≫ s₃ = n)
    (h₄ : a ≫ t ≫ n = 𝟙 P) : 𝟙 P = (((a ≫ c) ≫ s₁) ≫ s₂) ≫ s₃ := by
  rw [← h₄, ← h₃, ← h₂]
  simp only [Category.assoc]
  rw [reassoc_of% h₁]

section Chart

variable {X X'V X'W : AlgebraicSpaces B S hS} {iW : X ⟶ X'W} (hiW : IsThickeningHom B S hS iW)
  {qV : X'V ⟶ X} (hqV : yoneda.relativelyRepresentable qV.hom)
  {H : X'W ⟶ X'V} (hH : yoneda.relativelyRepresentable H.hom)
  (hiV : IsThickeningHom B S hS (iW ≫ H)) (hV : (iW ≫ H) ≫ qV = 𝟙 X)
  (hqW : yoneda.relativelyRepresentable (H ≫ qV).hom) (hW : iW ≫ H ≫ qV = 𝟙 X)

/-- **The two retractions of charts agree through `H`**: `U ≅ (U ×_X X'_V) ×_{X'_V} X` followed by
the comparison with `((U ×_X X'_V) ×_{X'_V} X'_W) ×_{X'_W} X` is `U ≅ (U ×_X X'_W) ×_{X'_W} X`
followed by the base change along `i_W` of `U ×_X X'_W ⟶ (U ×_X X'_V) ×_{X'_V} X'_W`. -/
theorem smallBaseChangeRetractionIso_inv_comp_chartCompIso (U : SmallEtale B S hS X.1) :
    (smallBaseChangeRetractionIso B S hS (iW ≫ H) qV hV hiV.isClosedImmersion.rep hqV).inv.app U ≫
        (smallBaseChangeChartCompIso B S hS iW H hiW.isClosedImmersion.rep hH
          hiV.isClosedImmersion.rep).hom.app ((smallBaseChange B S hS qV hqV).obj U) =
      (smallBaseChangeRetractionIso B S hS iW (H ≫ qV) hW hiW.isClosedImmersion.rep hqW).inv.app U ≫
        (smallBaseChange B S hS iW hiW.isClosedImmersion.rep).map
          ((smallBaseChangeChartCompIso B S hS H qV hH hqV hqW).hom.app U) := by
  refine smallBaseChange_obj_hom_ext B S hS iW hiW.isClosedImmersion.rep _ _ ?_
  refine hH.hom_ext ((representablePullback_snd_comp_hom B S hS iW _ _
    (CostructuredArrow.w _)).trans (representablePullback_snd_comp_hom B S hS iW _ _
    (CostructuredArrow.w _)).symm) ?_
  refine hqV.hom_ext ((representablePullback_snd_comp_hom B S hS H hH
    (V := (smallBaseChange B S hS qV hqV).obj U) _
    (representablePullback_snd_comp_hom B S hS iW hiW.isClosedImmersion.rep
      (V := (smallBaseChange B S hS H hH).obj ((smallBaseChange B S hS qV hqV).obj U)) _
      (CostructuredArrow.w _))).trans
    (representablePullback_snd_comp_hom B S hS H hH
    (V := (smallBaseChange B S hS qV hqV).obj U) _
    (representablePullback_snd_comp_hom B S hS iW hiW.isClosedImmersion.rep
      (V := (smallBaseChange B S hS H hH).obj ((smallBaseChange B S hS qV hqV).obj U)) _
      (CostructuredArrow.w _))).symm) ?_
  have e1 : ((smallBaseChangeChartCompIso B S hS iW H hiW.isClosedImmersion.rep hH
        hiV.isClosedImmersion.rep).hom.app ((smallBaseChange B S hS qV hqV).obj U)).hom.left ≫
        hiW.isClosedImmersion.rep.snd ((smallBaseChange B S hS H hH).obj
          ((smallBaseChange B S hS qV hqV).obj U)).1.hom =
      chartBaseChangeMiddle B S hS iW H hH hiV.isClosedImmersion.rep
        ((smallBaseChange B S hS qV hqV).obj U) :=
    chartBaseChangeCompComparison_comp_snd B S hS iW H hiW.isClosedImmersion.rep hH
      hiV.isClosedImmersion.rep ((smallBaseChange B S hS qV hqV).obj U)
  have e2 := chartBaseChangeMiddle_snd B S hS iW H hH hiV.isClosedImmersion.rep
    ((smallBaseChange B S hS qV hqV).obj U)
  have e3 : ((smallBaseChangeRetractionIso B S hS (iW ≫ H) qV hV hiV.isClosedImmersion.rep
        hqV).inv.app U).hom.left ≫ hiV.isClosedImmersion.rep.snd (hqV.fst U.1.hom) ≫
        hqV.snd U.1.hom = 𝟙 U.1.left :=
    congrArg (fun k => k.hom.left)
      ((smallBaseChangeRetractionIso B S hS (iW ≫ H) qV hV hiV.isClosedImmersion.rep
        hqV).inv_hom_id_app U)
  have f1 := smallBaseChange_map_snd B S hS iW hiW.isClosedImmersion.rep
    ((smallBaseChangeChartCompIso B S hS H qV hH hqV hqW).hom.app U)
  have f2 : ((smallBaseChangeChartCompIso B S hS H qV hH hqV hqW).hom.app U).hom.left ≫
        hH.snd ((smallBaseChange B S hS qV hqV).obj U).1.hom =
      chartBaseChangeMiddle B S hS H qV hqV hqW U :=
    chartBaseChangeCompComparison_comp_snd B S hS H qV hH hqV hqW U
  have f3 := chartBaseChangeMiddle_snd B S hS H qV hqV hqW U
  have f4 : ((smallBaseChangeRetractionIso B S hS iW (H ≫ qV) hW hiW.isClosedImmersion.rep
        hqW).inv.app U).hom.left ≫ hiW.isClosedImmersion.rep.snd (hqW.fst U.1.hom) ≫
        hqW.snd U.1.hom = 𝟙 U.1.left :=
    congrArg (fun k => k.hom.left)
      ((smallBaseChangeRetractionIso B S hS iW (H ≫ qV) hW hiW.isClosedImmersion.rep
        hqW).inv_hom_id_app U)
  refine (?_ : _ = 𝟙 U.1.left).trans (?_ : 𝟙 U.1.left = _)
  · simp only [ObjectProperty.FullSubcategory.comp_hom, CostructuredArrow.comp_left]
    exact comp_four_eq_id_of_eq e1 e2 e3
  · simp only [ObjectProperty.FullSubcategory.comp_hom, CostructuredArrow.comp_left]
    exact id_eq_comp_four_of_eq f1 f2 f3 f4

end Chart

section Generic

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {E : Type*} [Category* E]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
  (A : Type*) [Category* A]

/-- A composite of morphisms of sheaves, on sections. -/
theorem sheaf_comp_hom_app_eq {C : Type*} [Category* C] {J : GrothendieckTopology C} {A : Type*}
    [Category* A] {P Q T : Sheaf J A} (f : P ⟶ Q) (g : Q ⟶ T) (U : Cᵒᵖ)
    {a : P.obj.obj U ⟶ Q.obj.obj U} {b : Q.obj.obj U ⟶ T.obj.obj U} (ha : f.hom.app U = a)
    (hb : g.hom.app U = b) :
    (f ≫ g).hom.app U = a ≫ b := by
  rw [← ha, ← hb]
  rfl

/-- A composite `L ≫ d` with `L = a ≫ b ≫ c`, `c ≫ d = e ≫ f` and `b ≫ e = g ≫ k` is
`(a ≫ g) ≫ k ≫ f`. -/
theorem comp_eq_comp_of_factors {𝒞 : Type*} [Category* 𝒞] {X₀ X₁ X₂ X₃ X₄ Y₂ Y₃ : 𝒞}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) (L : X₀ ⟶ X₃) (hL : L = a ≫ b ≫ c)
    (e : X₂ ⟶ Y₃) (f : Y₃ ⟶ X₄) (hcd : c ≫ d = e ≫ f) (g : X₁ ⟶ Y₂) (k : Y₂ ⟶ Y₃)
    (hbe : b ≫ e = g ≫ k) :
    L ≫ d = (a ≫ g) ≫ k ≫ f := by
  subst hL
  simp only [Category.assoc]
  rw [hcd, reassoc_of% hbe]

/-- Restriction along `F` of the action of `τ : G ⟶ G'` on restrictions, on sections. -/
theorem sheafPushforwardContinuous_map_natTrans_app_hom_app (F : C ⥤ D) {G G' : D ⥤ E}
    (τ : G ⟶ G') [F.IsContinuous J K] [G.IsContinuous K L] [G'.IsContinuous K L]
    (P : Sheaf L A) (U : Cᵒᵖ) :
    ((F.sheafPushforwardContinuous A J K).map
      ((Functor.sheafPushforwardContinuousNatTrans τ A K L).app P)).hom.app U =
      P.obj.map (τ.app (F.obj U.unop)).op := rfl

/-- The action of `τ : F ⟶ F'` on restrictions, at a restriction along `G`, on sections. -/
theorem sheafPushforwardContinuousNatTrans_app_pushforward_hom_app {F F' : C ⥤ D} (τ : F ⟶ F')
    (G : D ⥤ E) [F.IsContinuous J K] [F'.IsContinuous J K] [G.IsContinuous K L]
    (P : Sheaf L A) (U : Cᵒᵖ) :
    ((Functor.sheafPushforwardContinuousNatTrans τ A J K).app
      ((G.sheafPushforwardContinuous A K L).obj P)).hom.app U =
      P.obj.map (G.map (τ.app U.unop)).op := rfl

/-- **Two retractions of sites agreeing through a comparison**, on restrictions of sheaves: for
`η_V : 𝟭 ⟶ q_V ⋙ i_V`, `η_W : 𝟭 ⟶ q_W ⋙ i_W`, `c : i_V ⟶ H ⋙ i_W` and `c' : q_W ⟶ q_V ⋙ H` with
`η_V ≫ c q_V = η_W ≫ i_W c'`, restricting along `q_V` the action of `c`, followed by the
identification `ε_V` given by `η_V`, is the action of `c'` followed by `ε_W`. -/
theorem sheafPushforwardContinuous_retraction_comparison {qV : C ⥤ D} {iV : D ⥤ C} {H : D ⥤ E}
    {iW : E ⥤ C} {qW : C ⥤ E} [qV.IsContinuous J K] [iV.IsContinuous K J] [H.IsContinuous K L]
    [iW.IsContinuous L J] [qW.IsContinuous J L] [(H ⋙ iW).IsContinuous K J]
    [(qV ⋙ H).IsContinuous J L] (c : iV ⟶ H ⋙ iW) (c' : qW ⟶ qV ⋙ H) (ηV : 𝟭 C ⟶ qV ⋙ iV)
    (ηW : 𝟭 C ⟶ qW ⋙ iW)
    (εV : iV.sheafPushforwardContinuous A K J ⋙ qV.sheafPushforwardContinuous A J K ⟶ 𝟭 _)
    (εW : iW.sheafPushforwardContinuous A L J ⋙ qW.sheafPushforwardContinuous A J L ⟶ 𝟭 _)
    (hεV : ∀ (R : Sheaf J A) (U : Cᵒᵖ), (εV.app R).hom.app U = R.obj.map (ηV.app U.unop).op)
    (hεW : ∀ (R : Sheaf J A) (U : Cᵒᵖ), (εW.app R).hom.app U = R.obj.map (ηW.app U.unop).op)
    (hc : ∀ U : C, ηV.app U ≫ c.app (qV.obj U) = ηW.app U ≫ iW.map (c'.app U)) (R : Sheaf J A) :
    (qV.sheafPushforwardContinuous A J K).map
        ((Functor.sheafPushforwardContinuousNatTrans c A K J).app R :
          (H.sheafPushforwardContinuous A K L).obj ((iW.sheafPushforwardContinuous A L J).obj R) ⟶
            (iV.sheafPushforwardContinuous A K J).obj R) ≫ εV.app R =
      ((Functor.sheafPushforwardContinuousNatTrans c' A J L).app
          ((iW.sheafPushforwardContinuous A L J).obj R) :
          (qV.sheafPushforwardContinuous A J K).obj
              ((H.sheafPushforwardContinuous A K L).obj
                ((iW.sheafPushforwardContinuous A L J).obj R)) ⟶
            (qW.sheafPushforwardContinuous A J L).obj
              ((iW.sheafPushforwardContinuous A L J).obj R)) ≫
        εW.app R := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U => ?_))
  refine (sheaf_comp_hom_app_eq _ _ U rfl (hεV R U)).trans (Eq.trans ?_
    (sheaf_comp_hom_app_eq _ _ U rfl (hεW R U)).symm)
  change R.obj.map (c.app (qV.obj U.unop)).op ≫ R.obj.map (ηV.app U.unop).op =
    R.obj.map (iW.map (c'.app U.unop)).op ≫ R.obj.map (ηW.app U.unop).op
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, hc]

/-- **Transposing a ring map through two retractions of sites**: under the identifications
`ε_V`, `ε_W` of `AlgebraicGeometry.Space.sheafPushforwardContinuous_retraction_comparison`, the
transpose along `q_V` of `𝒪_V ⟶ H_* 𝒪_W ⟶ H_* i_W^* R ⟶ i_V^* R` is
`q_{V*} 𝒪_V ⟶ q_{W*} 𝒪_W` followed by the transpose along `q_W` of `ψ : 𝒪_W ⟶ i_W^* R`, as soon
as the first map is `q_V` of the structure map followed by the action of `c'`. -/
theorem sheafPushforwardContinuous_retraction_transpose {qV : C ⥤ D} {iV : D ⥤ C} {H : D ⥤ E}
    {iW : E ⥤ C} {qW : C ⥤ E} [qV.IsContinuous J K] [iV.IsContinuous K J] [H.IsContinuous K L]
    [iW.IsContinuous L J] [qW.IsContinuous J L] [(H ⋙ iW).IsContinuous K J]
    [(qV ⋙ H).IsContinuous J L] (c : iV ⟶ H ⋙ iW) (c' : qW ⟶ qV ⋙ H) (ηV : 𝟭 C ⟶ qV ⋙ iV)
    (ηW : 𝟭 C ⟶ qW ⋙ iW)
    (εV : iV.sheafPushforwardContinuous A K J ⋙ qV.sheafPushforwardContinuous A J K ⟶ 𝟭 _)
    (εW : iW.sheafPushforwardContinuous A L J ⋙ qW.sheafPushforwardContinuous A J L ⟶ 𝟭 _)
    (hεV : ∀ (R : Sheaf J A) (U : Cᵒᵖ), (εV.app R).hom.app U = R.obj.map (ηV.app U.unop).op)
    (hεW : ∀ (R : Sheaf J A) (U : Cᵒᵖ), (εW.app R).hom.app U = R.obj.map (ηW.app U.unop).op)
    (hc : ∀ U : C, ηV.app U ≫ c.app (qV.obj U) = ηW.app U ≫ iW.map (c'.app U))
    {OV : Sheaf K A} {OW : Sheaf L A} (sharp : OV ⟶ (H.sheafPushforwardContinuous A K L).obj OW)
    (ρ : (qV.sheafPushforwardContinuous A J K).obj OV ⟶
      (qW.sheafPushforwardContinuous A J L).obj OW)
    (hρ : ρ = (qV.sheafPushforwardContinuous A J K).map sharp ≫
      ((Functor.sheafPushforwardContinuousNatTrans c' A J L).app OW :
        (qV.sheafPushforwardContinuous A J K).obj ((H.sheafPushforwardContinuous A K L).obj OW) ⟶
          (qW.sheafPushforwardContinuous A J L).obj OW))
    (R : Sheaf J A) (ψ : OW ⟶ (iW.sheafPushforwardContinuous A L J).obj R) :
    (qV.sheafPushforwardContinuous A J K).map
        (sharp ≫ (H.sheafPushforwardContinuous A K L).map ψ ≫
          (Functor.sheafPushforwardContinuousNatTrans c A K J).app R) ≫ εV.app R =
      ρ ≫ (qW.sheafPushforwardContinuous A J L).map ψ ≫ εW.app R := by
  subst hρ
  have hII := sheafPushforwardContinuous_retraction_comparison J K L A c c' ηV ηW εV εW hεV hεW hc R
  have hnat :
      (qV.sheafPushforwardContinuous A J K).map ((H.sheafPushforwardContinuous A K L).map ψ) ≫
        (Functor.sheafPushforwardContinuousNatTrans c' A J L).app
          ((iW.sheafPushforwardContinuous A L J).obj R) =
      (Functor.sheafPushforwardContinuousNatTrans c' A J L).app OW ≫
        (qW.sheafPushforwardContinuous A J L).map ψ :=
    (Functor.sheafPushforwardContinuousNatTrans c' A J L).naturality ψ
  exact comp_eq_comp_of_factors _ _ _ _ _
    ((Functor.map_comp _ _ _).trans (congrArg _ (Functor.map_comp _ _ _))) _ _ hII _ _ hnat

end Generic

/-- The chart identification `AlgebraicGeometry.Space.sheafPushforwardRetractionIso` on sections:
restriction along `U ≅ (U ×_X X') ×_{X'} X`. -/
theorem sheafPushforwardRetractionIso_hom_app_hom_app {X X' : AlgebraicSpaces B S hS}
    {i : X ⟶ X'} (hi : IsThickeningHom B S hS i) {q : X' ⟶ X} (h : i ≫ q = 𝟙 X)
    (hq : yoneda.relativelyRepresentable q.hom) (A : Type*) [Category* A]
    (R : Sheaf (SmallEtale.topology B S hS X.1) A) (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    ((sheafPushforwardRetractionIso B S hS hi h hq A).hom.app R).hom.app U =
      R.obj.map ((smallBaseChangeRetractionIso B S hS i q h hi.isClosedImmersion.rep hq).inv.app
        U.unop).op := by
  simp only [sheafPushforwardRetractionIso, Functor.sheafPushforwardContinuousId', Iso.trans_hom,
    NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom]
  refine (Category.id_comp _).trans ?_
  simp only [Functor.sheafPushforwardContinuousId, Iso.refl_hom,
    Functor.sheafPushforwardContinuousIso_hom, NatTrans.id_app,
    Functor.sheafPushforwardContinuousNatTrans_app_hom, Functor.whiskerRight_app, NatTrans.op_app,
    ObjectProperty.FullSubcategory.id_hom]
  exact Category.comp_id _

section Ring

variable {X X'V X'W : AlgebraicSpaces B S hS} {iW : X ⟶ X'W} (hiW : IsThickeningHom B S hS iW)
  {qV : X'V ⟶ X} (hqV : yoneda.relativelyRepresentable qV.hom)
  {H : X'W ⟶ X'V} (hH : yoneda.relativelyRepresentable H.hom)
  (hiV : IsThickeningHom B S hS (iW ≫ H)) (hV : (iW ≫ H) ≫ qV = 𝟙 X)
  (hqW : yoneda.relativelyRepresentable (H ≫ qV).hom) (hW : iW ≫ H ≫ qV = 𝟙 X)

attribute [local instance] isContinuous_smallBaseChange

/-- **Restriction along chart base change along `q_V`, then along `H`, is restriction along chart
base change along `H ≫ q_V`**, through `U ×_X X'_W ⟶ (U ×_X X'_V) ×_{X'_V} X'_W`
(`AlgebraicGeometry.Space.smallBaseChangeChartCompIso`). -/
def retractionChartCompPushforward
    (P : Sheaf (SmallEtale.topology B S hS X'W.1) CommRingCat.{u}) :
    ((smallBaseChange B S hS qV hqV).sheafPushforwardContinuous CommRingCat.{u}
        (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS X'V.1)).obj
        (((smallBaseChange B S hS H hH).sheafPushforwardContinuous CommRingCat.{u}
          (SmallEtale.topology B S hS X'V.1) (SmallEtale.topology B S hS X'W.1)).obj P) ⟶
      ((smallBaseChange B S hS (H ≫ qV) hqW).sheafPushforwardContinuous CommRingCat.{u}
        (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS X'W.1)).obj P :=
  (Functor.sheafPushforwardContinuousNatTrans
    (smallBaseChangeChartCompIso B S hS H qV hH hqV hqW).hom CommRingCat.{u}
    (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS X'W.1)).app P

/-- **The ring map of `H` over `X` factors through the chart comparison**: pulling functions on
`U ×_X X'_V` back to `U ×_X X'_W` is pulling them back to `(U ×_X X'_V) ×_{X'_V} X'_W` and then
along the comparison. -/
theorem thickeningRetractionRingMap_eq_sharp_comp :
    thickeningRetractionRingMap B S hS hqV hqW (rfl : H ≫ qV = H ≫ qV) =
      ((smallBaseChange B S hS qV hqV).sheafPushforwardContinuous CommRingCat.{u}
        (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS X'V.1)).map
          (smallBaseChangeSharpCommRingCat B S hS H hH) ≫
        retractionChartCompPushforward B S hS hqV hH hqW (structureSheaf B S hS X'W.1 X'W.2) := by
  ext U x
  have hm : ((smallBaseChangeChartCompIso B S hS H qV hH hqV hqW).hom.app U.unop).hom.left ≫
        hH.snd ((smallBaseChange B S hS qV hqV).obj U.unop).1.hom =
      thickeningRetractionChartMap B S hS hqV hqW (rfl : H ≫ qV = H ≫ qV) U.unop :=
    chartBaseChangeCompComparison_comp_snd B S hS H qV hH hqV hqW U.unop
  refine (thickeningRetractionRingMap_app_apply B S hS hqV hqW rfl U x).trans ?_
  refine (congrArg (fun m => (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map m).op).hom x)
    hm.symm).trans ?_
  exact Γ_map_toScheme_comp_apply B S hS _ _ x

/-- `AlgebraicGeometry.Space.squareZeroChartCompIso` at `i_V = i_W ≫ H` is
`AlgebraicGeometry.Space.smallBaseChangeChartCompIso`. -/
theorem squareZeroChartCompIso_rfl :
    squareZeroChartCompIso hiV hiW hH rfl =
      smallBaseChangeChartCompIso B S hS iW H hiW.isClosedImmersion.rep hH
        hiV.isClosedImmersion.rep := by
  ext V
  simp [squareZeroChartCompIso]

/-- The chart identity of
`AlgebraicGeometry.Space.smallBaseChangeRetractionIso_inv_comp_chartCompIso`, through
`AlgebraicGeometry.Space.squareZeroChartCompIso`. -/
theorem smallBaseChangeRetractionIso_inv_comp_squareZeroChartCompIso (U : SmallEtale B S hS X.1) :
    (smallBaseChangeRetractionIso B S hS (iW ≫ H) qV hV hiV.isClosedImmersion.rep hqV).inv.app U ≫
        (squareZeroChartCompIso hiV hiW hH rfl).hom.app ((smallBaseChange B S hS qV hqV).obj U) =
      (smallBaseChangeRetractionIso B S hS iW (H ≫ qV) hW hiW.isClosedImmersion.rep hqW).inv.app U ≫
        (smallBaseChange B S hS iW hiW.isClosedImmersion.rep).map
          ((smallBaseChangeChartCompIso B S hS H qV hH hqV hqW).hom.app U) := by
  rw [squareZeroChartCompIso_rfl]
  exact smallBaseChangeRetractionIso_inv_comp_chartCompIso B S hS hiW hqV hH hiV hV hqW hW U

/-- **The transpose of the ring map of `H` on the site of `X_V`**, for `i_V = i_W ≫ H` and
`q_W = H ≫ q_V`: transposed along `q_V`, `𝒪_{X_V} ⟶ H_* 𝒪_{X_W} ⟶ H_* i_W^* R ≅ i_V^* R` is
pullback of functions along `H` followed by the transpose of `ψ` along `q_W`. -/
theorem thickeningPushforwardRingMap_homEquiv_symm_of_comp
    {R : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    (ψ : structureSheaf B S hS X'W.1 X'W.2 ⟶
      (thickeningRetractionEquivalence B S hS hiW hW hqW CommRingCat.{u}).functor.obj R) :
    ((thickeningRetractionEquivalence B S hS hiV hV hqV CommRingCat.{u}).symm.toAdjunction.homEquiv
        (structureSheaf B S hS X'V.1 X'V.2) R).symm
        (thickeningPushforwardRingMap (hqV := hqV) hiV hV hiW hW hH rfl ψ) =
      thickeningRetractionRingMap B S hS hqV hqW (rfl : H ≫ qV = H ≫ qV) ≫
        ((thickeningRetractionEquivalence B S hS hiW hW hqW
          CommRingCat.{u}).symm.toAdjunction.homEquiv (structureSheaf B S hS X'W.1 X'W.2) R).symm
          ψ := by
  rw [thickeningRetractionEquivalence_homEquiv_symm, thickeningRetractionEquivalence_homEquiv_symm]
  exact sheafPushforwardContinuous_retraction_transpose (SmallEtale.topology B S hS X.1)
    (SmallEtale.topology B S hS X'V.1) (SmallEtale.topology B S hS X'W.1) CommRingCat.{u}
    (squareZeroChartCompIso hiV hiW hH rfl).hom
    (smallBaseChangeChartCompIso B S hS H qV hH hqV hqW).hom
    (smallBaseChangeRetractionIso B S hS (iW ≫ H) qV hV hiV.isClosedImmersion.rep hqV).inv
    (smallBaseChangeRetractionIso B S hS iW (H ≫ qV) hW hiW.isClosedImmersion.rep hqW).inv
    (sheafPushforwardRetractionIso B S hS hiV hV hqV CommRingCat.{u}).hom
    (sheafPushforwardRetractionIso B S hS hiW hW hqW CommRingCat.{u}).hom
    (sheafPushforwardRetractionIso_hom_app_hom_app B S hS hiV hV hqV CommRingCat.{u})
    (sheafPushforwardRetractionIso_hom_app_hom_app B S hS hiW hW hqW CommRingCat.{u})
    (smallBaseChangeRetractionIso_inv_comp_squareZeroChartCompIso B S hS hiW hqV hH hiV hV hqW hW)
    (smallBaseChangeSharpCommRingCat B S hS H hH) _
    (thickeningRetractionRingMap_eq_sharp_comp B S hS hqV hH hqW) R ψ

end Ring

section Naturality

open Deformation.Artin Deformation.ComplexLift Stacks.TensorByBaseModule

variable {B S hS} {k : Type u} [CommRing k] {toS : Spec (.of k) ⟶ S}
  {hk : B.Contains (Spec (.of k))}
  {V W : SiteModule k B}
  {X X'V X'W : AlgebraicSpaces B S hS} {p : X.1 ⟶ yoneda.obj (algebraOver k B S hS toS hk)}
  {iV : X ⟶ X'V} (hiV : IsThickeningHom B S hS iV)
  {qV : X'V ⟶ X} (hV : iV ≫ qV = 𝟙 X) {hqV : yoneda.relativelyRepresentable qV.hom}
  {p'V : X'V.1 ⟶ yoneda.obj (squareZeroOver k B S hS toS V)}
  {τV : squareZeroOver k B S hS toS V ⟶ algebraOver k B S hS toS hk}
  (hipV : iV.hom ≫ p'V = p ≫ yoneda.map (squareZeroArrow k B S hS toS hk V))
  (hpbV : IsPullback qV.hom p'V p (yoneda.map τV))
  (hβτV : squareZeroArrow k B S hS toS hk V ≫ τV = 𝟙 _)
  {iW : X ⟶ X'W} (hiW : IsThickeningHom B S hS iW)
  {qW : X'W ⟶ X} (hW : iW ≫ qW = 𝟙 X) {hqW : yoneda.relativelyRepresentable qW.hom}
  {p'W : X'W.1 ⟶ yoneda.obj (squareZeroOver k B S hS toS W)}
  {τW : squareZeroOver k B S hS toS W ⟶ algebraOver k B S hS toS hk}
  (hipW : iW.hom ≫ p'W = p ≫ yoneda.map (squareZeroArrow k B S hS toS hk W))
  (hpbW : IsPullback qW.hom p'W p (yoneda.map τW))
  (hβτW : squareZeroArrow k B S hS toS hk W ≫ τW = 𝟙 _)
  {H : X'W ⟶ X'V} (hH : yoneda.relativelyRepresentable H.hom) (hiH : iW ≫ H = iV)
  (f : V ⟶ W) (hHq : H ≫ qV = qW)
  (hgp : H.hom ≫ p'V = p'W ≫ yoneda.map (squareZeroOverMap k B S hS toS f))

include hHq hgp in
/-- **The ring map induced by `f : V ⟶ W` is the ring map of `H` on the site of `X_V`** (the
hypothesis `hg` of `AlgebraicGeometry.Space.squareZeroPullbackNaturalityIso` and
`AlgebraicGeometry.Space.squareZeroDerivedPullbackNaturality`): for `H : X_W ⟶ X_V` over `X`,
over `Spec k[W] ⟶ Spec k[V]` and compatible with the sections, the map
`𝒪_X[𝒪_X ⊗_k V] ⟶ 𝒪_X[𝒪_X ⊗_k W]` of `𝒪_X ⊗_k f`, read on `X_V` through
`AlgebraicGeometry.Space.squareZeroStructureSheafIso`, is
`AlgebraicGeometry.Space.thickeningPushforwardRingMap`. -/
theorem squareZeroStructureSheafIso_naturality :
    (squareZeroStructureSheafIso (hq := hqV) hiV hV hipV hpbV hβτV).hom ≫
        (thickeningRetractionEquivalence B S hS hiV hV hqV CommRingCat.{u}).functor.map
          (sqZeroExtSheafAnySiteMap ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
      (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
      (squareZeroCoefficientMap k B S hS toS hk p)).map f.hom)) =
      thickeningPushforwardRingMap (hqV := hqV) hiV hV hiW hW hH hiH
        (squareZeroStructureSheafIso (hq := hqW) hiW hW hipW hpbW hβτW).hom := by
  subst hiH hHq
  have G1 := squareZeroRetractionRingIso_naturality hqV hqW rfl hiV hV hiW hW f p hipV hpbV hβτV
    hipW hpbW hβτW rfl hgp
  have T := thickeningPushforwardRingMap_homEquiv_symm_of_comp B S hS hiW hqV hH hiV hV hqW hW
    (squareZeroStructureSheafIso (hq := hqW) hiW hW hipW hpbW hβτW).hom
  refine ((thickeningRetractionEquivalence B S hS hiV hV hqV
    CommRingCat.{u}).symm.toAdjunction.homEquiv _ _).symm.injective ?_
  refine (Adjunction.homEquiv_naturality_right_symm _ _ _).trans ?_
  refine (congrArg (· ≫ _) (Equiv.symm_apply_apply _ _)).trans ?_
  refine G1.trans ?_
  refine Eq.trans ?_ T.symm
  exact congrArg (_ ≫ ·) (Equiv.symm_apply_apply _ _).symm

/-- **`G2a` at the ring map of `f`**: the pushforward of modules along `H` is restriction of
scalars along the map induced by `𝒪_X ⊗_k f`, read through
`AlgebraicGeometry.Space.squareZeroModuleEquivalence` for `W` and `V`. -/
def squareZeroPushforwardNaturalityIsoOfMap :
    (squareZeroModuleEquivalence (hq := hqW) hiW hW hipW hpbW hβτW).functor ⋙
        smallBaseChangeModulePushforward.{u, u} B S hS H hH ≅
      SheafOfModules.restrictScalars
          ((sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
            (sqZeroExtSheafAnySiteMap ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
      (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
      (squareZeroCoefficientMap k B S hS toS hk p)).map f.hom))) ⋙
        (squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).functor :=
  squareZeroPushforwardNaturalityIso hiV hV hipV hpbV hβτV hiW hW hipW hpbW hβτW hH hiH
    (squareZeroStructureSheafIso_naturality hiV hV hipV hpbV hβτV hiW hW hipW hpbW hβτW hH hiH f
      hHq hgp)

/-- **Stacks 0DLL, `G2`, at the ring map of `f`**: the pullback of modules along `H` is extension
of scalars along the map induced by `𝒪_X ⊗_k f`, read through
`AlgebraicGeometry.Space.squareZeroModuleEquivalence` for `V` and `W`. -/
def squareZeroPullbackNaturalityIsoOfMap :
    (squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).functor ⋙
        (modulePullbackDataTopos B S hS).pull H ≅
      extensionOfScalars (sqZeroExtSheafAnySiteMap
        ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
      (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
      (squareZeroCoefficientMap k B S hS toS hk p)).map f.hom)) ⋙
        (squareZeroModuleEquivalence (hq := hqW) hiW hW hipW hpbW hβτW).functor :=
  squareZeroPullbackNaturalityIso hiV hV hipV hpbV hβτV hiW hW hipW hpbW hβτW hH hiH
    (squareZeroStructureSheafIso_naturality hiV hV hipV hpbV hβτV hiW hW hipW hpbW hβτW hH hiH f
      hHq hgp)

/-- **`G2` on cochain complexes, at the ring map of `f`**: the pullback of cochain complexes of
modules along `H` is extension of scalars along the map induced by `𝒪_X ⊗_k f`, read through
`AlgebraicGeometry.Space.squareZeroModuleEquivalence` for `V` and `W`. -/
def squareZeroComplexPullbackNaturalityIsoOfMap :
    (squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).functor.mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        ((modulePullbackDataTopos B S hS).pull H).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      extensionOfScalarsCochainComplex (SmallEtale.topology B S hS X.1)
          (sqZeroExtSheafAnySiteMap ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
      (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
      (squareZeroCoefficientMap k B S hS toS hk p)).map f.hom)) ⋙
        (squareZeroModuleEquivalence (hq := hqW) hiW hW hipW hpbW
          hβτW).functor.mapHomologicalComplex (ComplexShape.up ℤ) :=
  squareZeroComplexPullbackNaturalityIso hiV hV hipV hpbV hβτV hiW hW hipW hpbW hβτW hH hiH
    (squareZeroStructureSheafIso_naturality hiV hV hipV hpbV hβτV hiW hW hipW hpbW hβτW hH hiH f
      hHq hgp)

section Derived

attribute [local instance 10000] HasDerivedCategory.standard

variable [hDV : HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
      (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
      (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj))))]
  [hDW : HasDerivedCategory.{d'} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
      (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
      (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj))))]

/-- **Stacks 0DLL, `G3` (`χ`), at the ring map of `f`**: the derived base change along the map
induced by `𝒪_X ⊗_k f`, followed by the derived equivalence for `W`, is the derived equivalence for
`V` followed by the derived pullback along `H`. -/
def squareZeroDerivedPullbackNaturalityOfMap :
    derivedExtensionOfScalars.{d, d'} (sqZeroExtSheafAnySiteMap
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
      (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
      (squareZeroCoefficientMap k B S hS toS hk p)).map f.hom)) ⋙
        (squareZeroDerivedEquivalence (hq := hqW) hiW hW hipW hpbW hβτW).functor ≅
      (squareZeroDerivedEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).functor ⋙
        derivedPull B S hS (hasDerivedModulePullbacks B S hS) H :=
  squareZeroDerivedPullbackNaturality hiV hV hipV hpbV hβτV hiW hW hipW hpbW hβτW hH hiH
    (squareZeroStructureSheafIso_naturality hiV hV hipV hpbV hβτV hiW hW hipW hpbW hβτW hH hiH f
      hHq hgp)

end Derived

end Naturality

end AlgebraicGeometry.Space

end
