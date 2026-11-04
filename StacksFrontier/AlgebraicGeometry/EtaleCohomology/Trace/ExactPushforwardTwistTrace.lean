module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExactTwistTrace
public import StacksFrontier.Homology.HomComplex.DerivedAdjunctionResolution
public import StacksFrontier.Homology.Perfect.LargeUniverse

/-!
# Twisted traces along an exact functor preserving injectives

Let `G : C' ⥤ C` be an exact functor between abelian categories with enough injectives which
preserves injective objects (in the application, the direct image along a closed immersion), and
let twists `P`, `P'`, functors `F₁`, `F₁'` and identifications `θ : P ⋙ F₁ ≅ F₁`,
`θ' : P' ⋙ F₁' ≅ F₁'` be given together with `γ : G ⋙ F₁ ≅ F₁'` and `ρ : P' ⋙ G ⟶ G ⋙ P`
compatible with `θ` and `θ'`.  Then for every bounded below complex `K'` with a twist `τ'` the
trace of the derived twisted endomorphism of `RF₂(RF₁(G K'))` attached to `G(τ') ≫ ρ` is the trace
of the one of `RF₂(RF₁'(K'))` attached to `τ'`.  Both are computed on an injective resolution of
`K'` and its image under `G`.

This is the abstract form of the compatibility of the canonical Frobenius trace with the direct
image along a closed immersion, used in Steps 1 and 2 of the proof of [Stacks, Tag 03UG].

## Main results

* `CategoryTheory.Functor.exists_twist_lift_of_injectiveResolution`: a twist of a bounded below
  complex lifts to an injective resolution.
* `CategoryTheory.Functor.perfectDerivedTrace_derivedTwistEndo_map_eq`: the trace comparison.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.FilteredDerived

attribute [local instance] HasDerivedCategory.standard

universe u v u₁ v₁

namespace CategoryTheory.Functor

section Lift

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [EnoughInjectives C] (P : C ⥤ C)
  [P.Additive] [P.PreservesInjectiveObjects]

/-- **A twist lifts to an injective resolution.**  For a bounded below complex `K` and a morphism
`τ : K ⟶ P(K)` there are a quasi-isomorphism `ψ : K ⟶ T` into a bounded below complex of
injectives and a twist `g` of `T` with `τ ≫ P(ψ) = ψ ≫ g` in the derived category. -/
theorem exists_twist_lift_of_injectiveResolution (K : CochainComplex.Plus C)
    (τ : K ⟶ P.mapCochainComplexPlus.obj K) :
    ∃ (T : CochainComplex.Plus C) (ψ : K ⟶ T) (_ : QuasiIso ψ.hom)
      (_ : ∀ n, Injective (T.obj.X n)) (g : T ⟶ P.mapCochainComplexPlus.obj T),
      DerivedCategory.Plus.Q.map (τ ≫ P.mapCochainComplexPlus.map ψ) =
        DerivedCategory.Plus.Q.map (ψ ≫ g) := by
  obtain ⟨a, ha⟩ := K.property
  obtain ⟨R, -, -⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE a K.obj
  let T : CochainComplex.Plus C := ⟨R.cocomplex, R.boundedBelow⟩
  let ψ : K ⟶ T := ObjectProperty.homMk R.ι
  have hq : QuasiIso ψ.hom := inferInstanceAs (QuasiIso R.ι)
  have hinj : ∀ n, Injective (T.obj.X n) := fun n => inferInstanceAs (Injective (R.cocomplex.X n))
  have : ∀ n, Injective ((P.mapCochainComplexPlus.obj T).obj.X n) := fun n =>
    inferInstanceAs (Injective (P.obj (R.cocomplex.X n)))
  have : IsIso (DerivedCategory.Q.map ψ.hom) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ ψ.hom).2 hq
  obtain ⟨b, hb⟩ := (P.mapCochainComplexPlus.obj T).property
  have := CochainComplex.isKInjective_of_injective (P.mapCochainComplexPlus.obj T).obj b
  obtain ⟨g, hg⟩ := StacksDraft.DerivedHom.exists_eq_Q_map_of_isKInjective T.obj
    (P.mapCochainComplexPlus.obj T).obj
    (CategoryTheory.inv (DerivedCategory.Q.map ψ.hom) ≫
      DerivedCategory.Q.map (τ ≫ P.mapCochainComplexPlus.map ψ).hom)
  refine ⟨T, ψ, hq, hinj, ObjectProperty.homMk g, DerivedCategory.Plus.ι.map_injective ?_⟩
  show DerivedCategory.Q.map (τ ≫ P.mapCochainComplexPlus.map ψ).hom =
    DerivedCategory.Q.map (ψ.hom ≫ g)
  rw [DerivedCategory.Q.map_comp ψ.hom g, hg, IsIso.hom_inv_id_assoc]

end Lift

section Transfer

variable {R : Type u} [Ring R] {C C' D : Type u₁} [Category.{v₁} C] [Category.{v₁} C']
  [Category.{v₁} D] [Abelian C] [Abelian C'] [Abelian D] [EnoughInjectives C]
  [EnoughInjectives C'] [EnoughInjectives D]
  (P : C ⥤ C) (F₁ : C ⥤ D) (P' : C' ⥤ C') (F₁' : C' ⥤ D) (F₂ : D ⥤ ModuleCat.{max u v} R)
  (G : C' ⥤ C) [P.Additive] [F₁.Additive] [P'.Additive] [F₁'.Additive] [F₂.Additive] [G.Additive]
  [P.PreservesInjectiveObjects] [P'.PreservesInjectiveObjects] [F₁.PreservesInjectiveObjects]
  [F₁'.PreservesInjectiveObjects] [G.PreservesInjectiveObjects]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (θ : P ⋙ F₁ ≅ F₁) (θ' : P' ⋙ F₁' ≅ F₁') (γ : G ⋙ F₁ ≅ F₁') (ρ : P' ⋙ G ⟶ G ⋙ P)

/-- The comparison `G(P'(K')) ⟶ P(G(K'))` induced by `ρ`, as a morphism of bounded below
complexes. -/
abbrev twistTransferMap (K' : CochainComplex.Plus C') :
    G.mapCochainComplexPlus.obj (P'.mapCochainComplexPlus.obj K') ⟶
      P.mapCochainComplexPlus.obj (G.mapCochainComplexPlus.obj K') :=
  ObjectProperty.homMk ((NatTrans.mapHomologicalComplex ρ _).app K'.obj)

private lemma transferChase {A B : Type*} [Category A] [Category B] (Q : A ⥤ B)
    {X₀ X₁ X₂ X₃ X₄ X₅ : A}
    (a : X₀ ⟶ X₁) (rK : X₁ ⟶ X₂) (b : X₂ ⟶ X₃) (c : X₁ ⟶ X₄) (rT : X₄ ⟶ X₃) (d : X₀ ⟶ X₅)
    (e : X₅ ⟶ X₄) (h : Q.map (a ≫ c) = Q.map (d ≫ e)) (hn : rK ≫ b = c ≫ rT) :
    Q.map ((a ≫ rK) ≫ b) = Q.map (d ≫ e ≫ rT) := by
  rw [Category.assoc, hn, ← Category.assoc, Q.map_comp, h, ← Q.map_comp, Category.assoc]

/-- A diagram chase: `F` of `a ≫ r`, then `θ` and `γ`, equals `γ₁ ≫ g' ≫ θ'`, given the two squares
`F(r) ≫ θ ≫ γ = γ₂ ≫ θ'` and `F(a) ≫ γ₂ = γ₁ ≫ g'`. -/
lemma transferChase₂ {A B : Type*} [Category A] [Category B] (F : A ⥤ B) {X Y Z : A}
    {W V U U' : B} (a : X ⟶ Y) (r : Y ⟶ Z) (θ : F.obj Z ⟶ W) (γ : W ⟶ V) (γ₁ : F.obj X ⟶ U)
    (g' : U ⟶ U') (γ₂ : F.obj Y ⟶ U') (θ' : U' ⟶ V) (h₁ : F.map r ≫ θ ≫ γ = γ₂ ≫ θ')
    (h₂ : F.map a ≫ γ₂ = γ₁ ≫ g') :
    (F.map (a ≫ r) ≫ θ) ≫ γ = γ₁ ≫ g' ≫ θ' := by
  rw [F.map_comp, Category.assoc, Category.assoc, h₁, reassoc_of% h₂]

omit [EnoughInjectives C] [EnoughInjectives C'] [G.PreservesInjectiveObjects] in
/-- An equality in the derived category is preserved by an exact functor applied termwise. -/
lemma Q_map_mapHomologicalComplex_eq {X Y : CochainComplex C' ℤ} {a b : X ⟶ Y}
    (h : DerivedCategory.Q.map a = DerivedCategory.Q.map b) :
    DerivedCategory.Q.map ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map a) =
      DerivedCategory.Q.map ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map b) := by
  have ha := G.mapDerivedCategoryFactors_hom_naturality a
  have hb := G.mapDerivedCategoryFactors_hom_naturality b
  rw [h] at ha
  rw [← cancel_epi (G.mapDerivedCategoryFactors.hom.app X), ← ha, hb]

/-- A quasi-isomorphism into a complex of injectives stays one after applying an exact functor
preserving injectives termwise. -/
private lemma map_resolution {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (H : A ⥤ B) [H.Additive] [H.PreservesInjectiveObjects] [PreservesFiniteLimits H]
    [PreservesFiniteColimits H] {K T : CochainComplex.Plus A} (ψ : K ⟶ T) (hq : QuasiIso ψ.hom)
    (hinj : ∀ n, Injective (T.obj.X n)) :
    QuasiIso (H.mapCochainComplexPlus.map ψ).hom ∧
      ∀ n, Injective ((H.mapCochainComplexPlus.obj T).obj.X n) :=
  ⟨inferInstanceAs (QuasiIso ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ.hom)),
    fun n => inferInstanceAs (Injective (H.obj (T.obj.X n)))⟩

omit [P.PreservesInjectiveObjects] [P'.PreservesInjectiveObjects] in
include γ in
/-- **Perfectness transfers along an exact functor preserving injectives**:
`RF₂(RF₁(G K'))` is perfect exactly when `RF₂(RF₁'(K'))` is. -/
lemma isPerfect_rightDerived_map_iff (K' : CochainComplex.Plus C') :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁.rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj (G.mapCochainComplexPlus.obj K'))))) ↔
      StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁'.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K')))) := by
  obtain ⟨T, ψ, hq, hinj, -, -⟩ := exists_twist_lift_of_injectiveResolution (𝟭 C') K' (𝟙 _)
  obtain ⟨hqG, hinjG⟩ := map_resolution G ψ hq hinj
  let e := twistResolutionIso F₁ F₂ (G.mapCochainComplexPlus.map ψ) hinjG ≪≫
    DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex (Functor.isoWhiskerRight γ F₂) _).app T.obj) ≪≫
    (twistResolutionIso F₁' F₂ ψ hinj).symm
  exact ⟨fun h => StacksDraft.Perfect.isPerfect_of_iso e.symm h,
    fun h => StacksDraft.Perfect.isPerfect_of_iso e h⟩

variable (hθ : ∀ X, F₁.map (ρ.app X) ≫ θ.hom.app (G.obj X) ≫ γ.hom.app X =
  γ.hom.app (P'.obj X) ≫ θ'.hom.app X)

include hθ in
/-- **The twisted trace along an exact functor preserving injectives.**  The trace of the derived
twisted endomorphism of `RF₂(RF₁(G K'))` attached to `G(τ') ≫ ρ` equals the trace of the one of
`RF₂(RF₁'(K'))` attached to `τ'`. -/
theorem perfectDerivedTrace_derivedTwistEndo_map_eq (K' : CochainComplex.Plus C')
    (τ' : K' ⟶ P'.mapCochainComplexPlus.obj K')
    (hK : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁.rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj (G.mapCochainComplexPlus.obj K'))))))
    (hK' : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁'.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K'))))) :
    perfectDerivedTrace R ⟨_, hK⟩ (DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ
        (G.mapCochainComplexPlus.obj K')
        (G.mapCochainComplexPlus.map τ' ≫ twistTransferMap P P' G ρ K'))) =
      perfectDerivedTrace R ⟨_, hK'⟩
        (DerivedCategory.Plus.ι.map (derivedTwistEndo P' F₁' F₂ θ' K' τ')) := by
  obtain ⟨T, ψ, hq, hinj, g, hg⟩ := exists_twist_lift_of_injectiveResolution P' K' τ'
  have hT' := StacksDraft.Perfect.isPerfect_of_iso (twistResolutionIso F₁' F₂ ψ hinj).symm hK'
  rw [perfectDerivedTrace_derivedTwistEndo_eq P' F₁' F₂ θ' ψ hinj τ' g hg hK' hT']
  obtain ⟨hqG, hinjG⟩ := map_resolution G ψ hq hinj
  have hgG : DerivedCategory.Plus.Q.map ((G.mapCochainComplexPlus.map τ' ≫
      twistTransferMap P P' G ρ K') ≫ P.mapCochainComplexPlus.map (G.mapCochainComplexPlus.map ψ)) =
      DerivedCategory.Plus.Q.map (G.mapCochainComplexPlus.map ψ ≫
        (G.mapCochainComplexPlus.map g ≫ twistTransferMap P P' G ρ T)) := by
    apply DerivedCategory.Plus.ι.map_injective
    have h₀ : DerivedCategory.Q.map (τ' ≫ P'.mapCochainComplexPlus.map ψ).hom =
        DerivedCategory.Q.map (ψ ≫ g).hom := DerivedCategory.Plus.ι.congr_map hg
    have h₁ := Q_map_mapHomologicalComplex_eq G h₀
    have hn := NatTrans.mapHomologicalComplex_naturality (c := ComplexShape.up ℤ) ρ ψ.hom
    show DerivedCategory.Q.map (((G.mapHomologicalComplex _).map τ'.hom ≫
        (NatTrans.mapHomologicalComplex ρ _).app K'.obj) ≫
          ((G ⋙ P).mapHomologicalComplex _).map ψ.hom) =
      DerivedCategory.Q.map ((G.mapHomologicalComplex _).map ψ.hom ≫
        (G.mapHomologicalComplex _).map g.hom ≫ (NatTrans.mapHomologicalComplex ρ _).app T.obj)
    exact transferChase DerivedCategory.Q _ _ _ _ _ _ _
      ((congrArg DerivedCategory.Q.map (Functor.map_comp _ _ _)).symm.trans
        (h₁.trans (congrArg DerivedCategory.Q.map (Functor.map_comp _ _ _)))) hn.symm
  have hTG := StacksDraft.Perfect.isPerfect_of_iso
    (twistResolutionIso F₁ F₂ (G.mapCochainComplexPlus.map ψ) hinjG).symm hK
  rw [perfectDerivedTrace_derivedTwistEndo_eq P F₁ F₂ θ (G.mapCochainComplexPlus.map ψ) hinjG _ _
    hgG hK hTG]
  refine perfectDerivedTrace_congr R _ _ (DerivedCategory.Q.mapIso
    ((NatIso.mapHomologicalComplex (Functor.isoWhiskerRight γ F₂) _).app T.obj)) _ _ ?_
  refine (DerivedCategory.Q.map_comp _ _).symm.trans
    ((congrArg DerivedCategory.Q.map ?_).trans (DerivedCategory.Q.map_comp _ _))
  ext n : 1
  have h₁ := hθ (T.obj.X n)
  have h₂ := γ.hom.naturality (g.hom.f n)
  show F₂.map (F₁.map (G.map (g.hom.f n) ≫ ρ.app (T.obj.X n)) ≫
      θ.hom.app (G.obj (T.obj.X n))) ≫ F₂.map (γ.hom.app (T.obj.X n)) =
    F₂.map (γ.hom.app (T.obj.X n)) ≫ F₂.map (F₁'.map (g.hom.f n) ≫ θ'.hom.app (T.obj.X n))
  rw [← F₂.map_comp, ← F₂.map_comp]
  congr 1
  dsimp only [Functor.comp_map] at h₂
  exact transferChase₂ F₁ _ _ _ _ _ _ _ _ h₁ h₂

end Transfer

end CategoryTheory.Functor

end
