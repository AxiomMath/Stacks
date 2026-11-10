module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.DerivedComplete.CechCompletion
public import StacksFrontier.Homology.HomComplex.DerivedAdjunction

section




/-!
# Derived completion and derived Hom

For a finitely generated ideal of a commutative ring, derived completion commutes with derived
Hom in the target. Moreover, completing the source does not change derived Hom into a derived
complete target.

## Main results

* `DerivedHomCechCompletion.derivedHom_cechCompletion`: for a finite family `f` generating an
  ideal of `A`, `RHom_A(K, L)^∧ ≅ RHom_A(K, L^∧)` naturally, and precomposition with the
  completion unit `K ⟶ K^∧` gives a natural isomorphism `RHom_A(K^∧, L^∧) ≅ RHom_A(K, L^∧)`.

## References

* [The Stacks Project, Tag 0A6E](https://stacks.math.columbia.edu/tag/0A6E)
* [Bhatt--Scholze, *Projectivity of the Witt vector affine Grassmannian*][BS]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

end

end

section


open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace DerivedHomCechCompletion

private lemma isIso_unit_app
    {C : Type u} [Category.{v} C] (F : C ⥤ C) (η : Functor.id C ⟶ F)
    (P : C → Prop) (hF : ∀ X, P (F.obj X))
    (hη : ∀ X E, P E → Function.Bijective (fun g : F.obj X ⟶ E ↦ η.app X ≫ g))
    (E : C) (hE : P E) : IsIso (η.app E) := by
  obtain ⟨g, hg⟩ := (hη E E hE).2 (𝟙 E)
  have h' : g ≫ η.app E = 𝟙 (F.obj E) := by
    apply (hη E (F.obj E) (hF E)).1
    dsimp only at hg
    change η.app E ≫ (g ≫ η.app E) = η.app E ≫ 𝟙 (F.obj E)
    rw [← Category.assoc, hg]
    simp
  exact ⟨⟨g, hg, h'⟩⟩

private lemma precomp_bijective_of_iso
    {C : Type u} [Category.{v} C] {X Y E E' : C} (f : X ⟶ Y) (e : E ≅ E')
    (h : Function.Bijective (fun g : Y ⟶ E ↦ f ≫ g)) :
    Function.Bijective (fun g : Y ⟶ E' ↦ f ≫ g) := by
  have hb := e.homToEquiv.bijective.comp (h.comp e.symm.homToEquiv.bijective)
  simpa only [Function.comp_def, Iso.homToEquiv, Iso.symm_hom,
    Equiv.coe_fn_mk, Category.assoc, Iso.inv_hom_id, Category.comp_id] using hb

section

variable {R : Type u} [CommRing R] [HasDerivedCategory.{v} (ModuleCat.{u} R)]
    (d : StacksDraft.DerivedHom.DerivedHomData R) (c : StacksDraft.DerivedHom.DerivedHomCurrying d)

private noncomputable def homExchangeIso (T K L : DerivedCategory (ModuleCat R)) :
    d.hom.obj (Opposite.op T, d.hom.obj (Opposite.op K, L)) ≅
      d.hom.obj (Opposite.op K, d.hom.obj (Opposite.op T, L)) :=
  c.iso T K L ≪≫
    d.hom.mapIso ((d.tensorSwap K T).op.prod (Iso.refl L)) ≪≫
    (c.iso K T L).symm

private lemma currying_naturality
    {K K' L L' M M' : DerivedCategory (ModuleCat R)}
    (f : K' ⟶ K) (g : L' ⟶ L) (h : M ⟶ M') :
    d.hom.map (Prod.mkHom f.op (d.hom.map (Prod.mkHom g.op h))) ≫ (c.iso K' L' M').hom =
      (c.iso K L M).hom ≫ d.hom.map (Prod.mkHom ((d.tensor.map (Prod.mkHom f g)).op) h) := by
  have split : d.hom.map (Prod.mkHom f.op (d.hom.map (Prod.mkHom g.op h))) =
      d.hom.map (Prod.mkHom f.op (𝟙 (d.hom.obj (Opposite.op L, M)))) ≫
        d.hom.map (Prod.mkHom (𝟙 (Opposite.op K')) (d.hom.map (Prod.mkHom g.op (𝟙 M)))) ≫
          d.hom.map (Prod.mkHom (𝟙 (Opposite.op K'))
            (d.hom.map (Prod.mkHom (𝟙 (Opposite.op L')) h))) := by
    simp only [← Functor.map_comp, prod_comp, Prod.mkHom, Category.id_comp, Category.comp_id]
  simp only [split, Category.assoc]
  rw [c.naturality_right, reassoc_of% (c.naturality_middle g),
    reassoc_of% (c.naturality_left f)]
  simp only [← Functor.map_comp, prod_comp, Prod.mkHom,
    Category.id_comp, Category.comp_id, ← op_comp]

private lemma homExchangeIso_naturality
    (T : DerivedCategory (ModuleCat R))
    {K K' L L' : DerivedCategory (ModuleCat R)} (f : K' ⟶ K) (g : L ⟶ L') :
    d.hom.map (Prod.mkHom (𝟙 (Opposite.op T)) (d.hom.map (Prod.mkHom f.op g))) ≫
        (homExchangeIso d c T K' L').hom =
      (homExchangeIso d c T K L).hom ≫
        d.hom.map (Prod.mkHom f.op (d.hom.map (Prod.mkHom (𝟙 (Opposite.op T)) g))) := by
  simp only [homExchangeIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.prod_hom, Iso.op_hom, Iso.refl_hom]
  apply (cancel_mono (c.iso K' T L').hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h₁ := currying_naturality d c (𝟙 T) f g
  have h₂ := currying_naturality d c f (𝟙 T) g
  simp only [op_id] at h₁ h₂
  rw [reassoc_of% h₁, h₂, Iso.inv_hom_id_assoc]
  simp only [← Functor.map_comp, prod_comp, Prod.mkHom,
    Category.id_comp, Category.comp_id, ← op_comp]
  rw [d.tensorSwap_naturality]

end

section

variable {R : Type u} [CommRing R] [HasDerivedCategory.{v} (ModuleCat.{w} R)]
    (d : StacksDraft.DerivedHom.DerivedHomAdjunction R)

private noncomputable def homTransposeEquiv (X K E : DerivedCategory (ModuleCat R)) :
    (X ⟶ d.hom.obj (Opposite.op K, E)) ≃ (K ⟶ d.hom.obj (Opposite.op X, E)) :=
  (d.homEquiv X K E).toEquiv |>.trans
    ((d.tensorSwap K X).symm.homFromEquiv.trans (d.homEquiv K X E).symm.toEquiv)

private lemma homTransposeEquiv_naturality
    {X K K' E : DerivedCategory (ModuleCat R)} (f : K' ⟶ K)
    (a : X ⟶ d.hom.obj (Opposite.op K, E)) :
    homTransposeEquiv d X K' E (a ≫ d.hom.map (Prod.mkHom f.op (𝟙 E))) =
      f ≫ homTransposeEquiv d X K E a := by
  apply (d.homEquiv K' X E).injective
  simp only [homTransposeEquiv, Equiv.trans_apply, AddEquiv.toEquiv_eq_coe,
    AddEquiv.coe_toEquiv, AddEquiv.apply_symm_apply,
    Iso.homFromEquiv_apply, Iso.symm_inv,
    d.homEquiv_dinaturality, d.homEquiv_naturality_left]
  exact (d.tensorSwap_naturality_assoc f (𝟙 X) (d.homEquiv X K E a)).symm

private lemma isIso_hom_map_unit
    (F : DerivedCategory (ModuleCat R) ⥤ DerivedCategory (ModuleCat R))
    (η : Functor.id _ ⟶ F) (P : DerivedCategory (ModuleCat R) → Prop)
    (hF : ∀ X, P (F.obj X))
    (hη : ∀ K E, P E → Function.Bijective (fun g : F.obj K ⟶ E ↦ η.app K ≫ g))
    (he : ∀ X E, F.obj (d.hom.obj (Opposite.op X, E)) ≅
      d.hom.obj (Opposite.op X, F.obj E))
    (K E : DerivedCategory (ModuleCat R)) (hE : P E) :
    IsIso (d.hom.map (Prod.mkHom (η.app K).op (𝟙 E))) := by
  have : IsIso (η.app E) := isIso_unit_app F η P hF hη E hE
  apply isIso_of_yoneda_map_bijective
  intro X
  let e : F.obj (d.hom.obj (Opposite.op X, E)) ≅
      d.hom.obj (Opposite.op X, E) :=
    he X E ≪≫ d.hom.mapIso ((Iso.refl (Opposite.op X)).prod (asIso (η.app E)).symm)
  apply (Equiv.comp_bijective _ (homTransposeEquiv d X K E)).mp
  change Function.Bijective (fun a ↦
    homTransposeEquiv d X K E (a ≫ d.hom.map (Prod.mkHom (η.app K).op (𝟙 E))))
  simp only [homTransposeEquiv_naturality]
  exact (precomp_bijective_of_iso (η.app K) e (hη K _ (hF _))).comp
    (homTransposeEquiv d X (F.obj K) E).bijective

end

private def homUnitNatTrans
    {C : Type u} [Category.{v} C] (H : Cᵒᵖ × C ⥤ C)
    (F : C ⥤ C) (η : Functor.id C ⟶ F) :
    (((CategoryTheory.Prod.fst Cᵒᵖ C ⋙ F.op).prod'
      (CategoryTheory.Prod.snd Cᵒᵖ C ⋙ F)) ⋙ H) ⟶
    ((CategoryTheory.Prod.fst Cᵒᵖ C).prod'
      (CategoryTheory.Prod.snd Cᵒᵖ C ⋙ F) ⋙ H) where
  app X := H.map ((η.app X.1.unop).op, 𝟙 (F.obj X.2))
  naturality {X Y} f := by
    dsimp
    rw [← H.map_comp, ← H.map_comp]
    congr 1
    apply Prod.ext
    · dsimp
      simpa only [Functor.id_map, op_comp, Quiver.Hom.op_unop] using
        congrArg Quiver.Hom.op (η.naturality f.1.unop).symm
    · simp

private lemma hom_reflection_iso
    {R : Type u} [CommRing R] [HasDerivedCategory.{v} (ModuleCat.{w} R)]
    (d : StacksDraft.DerivedHom.DerivedHomAdjunction R)
    (F : DerivedCategory (ModuleCat R) ⥤ DerivedCategory (ModuleCat R))
    (η : Functor.id _ ⟶ F) (P : DerivedCategory (ModuleCat R) → Prop)
    (hF : ∀ X, P (F.obj X))
    (hη : ∀ K E, P E → Function.Bijective (fun g : F.obj K ⟶ E ↦ η.app K ≫ g))
    (he : ∀ X E, F.obj (d.hom.obj (Opposite.op X, E)) ≅
      d.hom.obj (Opposite.op X, F.obj E)) :
    let C := DerivedCategory (ModuleCat R)
    ∃ e :
        ((((CategoryTheory.Prod.fst Cᵒᵖ C ⋙ F.op).prod'
            (CategoryTheory.Prod.snd Cᵒᵖ C ⋙ F)) ⋙ d.hom) ≅
          (((CategoryTheory.Prod.fst Cᵒᵖ C).prod'
            (CategoryTheory.Prod.snd Cᵒᵖ C ⋙ F)) ⋙ d.hom)),
      ∀ (K L : C), e.hom.app (Opposite.op K, L) =
        d.hom.map (Prod.mkHom (η.app K).op (𝟙 (F.obj L))) := by
  let α := homUnitNatTrans d.hom F η
  have (X : (DerivedCategory (ModuleCat R))ᵒᵖ × DerivedCategory (ModuleCat R)) :
      IsIso (α.app X) :=
    isIso_hom_map_unit d F η P hF hη he X.1.unop (F.obj X.2) (hF X.2)
  exact ⟨NatIso.ofComponents (fun X ↦ asIso (α.app X)) (fun g ↦ α.naturality g),
    fun _ _ ↦ rfl⟩

/-- For a finite family `f` generating an ideal of `A`, derived completion commutes naturally
with derived Hom in its target, and precomposition with the completion unit `K ⟶ K^∧` is a natural
isomorphism `RHom_A(K^∧, L^∧) ≅ RHom_A(K, L^∧)`. -/
private theorem derivedHom_cechCompletion_aux (A : Type u) [CommRing A] {r : ℕ}
    (f : Fin r → A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))] :
    let C := DerivedCategory (ModuleCat.{u} A)
    let D := StacksDraft.DerivedHom.derivedHomAdjunction (R := A)
    let F := CechCompletion.cechCompletionFunctor A f
    ∃ η : Functor.id C ⟶ F,
      (∀ K, IsDerivedComplete (Ideal.span (Set.range f)) (F.obj K)) ∧
      (∀ (K E : C), IsDerivedComplete (Ideal.span (Set.range f)) E →
        Function.Bijective (fun g : F.obj K ⟶ E ↦ η.app K ≫ g)) ∧
      Nonempty
        ((D.hom ⋙ F) ≅
          (((CategoryTheory.Prod.fst Cᵒᵖ C).prod'
            (CategoryTheory.Prod.snd Cᵒᵖ C ⋙ F)) ⋙ D.hom)) ∧
      ∃ e :
          ((((CategoryTheory.Prod.fst Cᵒᵖ C ⋙ F.op).prod'
              (CategoryTheory.Prod.snd Cᵒᵖ C ⋙ F)) ⋙ D.hom) ≅
            (((CategoryTheory.Prod.fst Cᵒᵖ C).prod'
              (CategoryTheory.Prod.snd Cᵒᵖ C ⋙ F)) ⋙ D.hom)),
        ∀ (K L : C), e.hom.app (Opposite.op K, L) =
          D.hom.map
            (show (Opposite.op (F.obj K), F.obj L) ⟶ (Opposite.op K, F.obj L) from
              ((η.app K).op, 𝟙 (F.obj L))) := by
  let D := StacksDraft.DerivedHom.derivedHomAdjunction (R := A)
  let c := StacksDraft.DerivedHom.derivedHomCurrying (R := A)
  let F := CechCompletion.cechCompletionFunctor A f
  let T := CechCompletion.extendedCechObject A f
  obtain ⟨η, hF, hη⟩ := CechCompletion.cechCompletion_isReflection A f
  refine ⟨η, hF, hη, ⟨NatIso.ofComponents
    (fun X ↦ homExchangeIso D c T X.1.unop X.2) ?_⟩, ?_⟩
  · intro X Y g
    simpa [CechCompletion.cechCompletionFunctor, D, T] using
      homExchangeIso_naturality D c T g.1.unop g.2
  · exact hom_reflection_iso D.toDerivedHomAdjunction F η _ hF hη (homExchangeIso D c T)

end DerivedHomCechCompletion



end

section


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace DerivedHomCechCompletion

/-- For a finite family `f` generating an ideal of `A`, derived completion commutes naturally
with derived Hom in its target: `RHom_A(K, L)^∧ ≅ RHom_A(K, L^∧)`. If `η : K ⟶ K^∧` is the
reflection unit, then precomposition with `η` is the natural isomorphism
`RHom_A(K^∧, L^∧) ≅ RHom_A(K, L^∧)`. -/
@[stacks 0A6E]
public theorem derivedHom_cechCompletion (A : Type u) [CommRing A] {r : ℕ}
    (f : Fin r → A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))] :
    let C := DerivedCategory (ModuleCat.{u} A)
    let D := StacksDraft.DerivedHom.derivedHomAdjunction (R := A)
    let F := CechCompletion.cechCompletionFunctor A f
    ∃ η : Functor.id C ⟶ F,
      (∀ K, IsDerivedComplete (Ideal.span (Set.range f)) (F.obj K)) ∧
      (∀ (K E : C), IsDerivedComplete (Ideal.span (Set.range f)) E →
        Function.Bijective (fun g : F.obj K ⟶ E ↦ η.app K ≫ g)) ∧
      Nonempty
        ((D.hom ⋙ F) ≅
          (((CategoryTheory.Prod.fst Cᵒᵖ C).prod'
            (CategoryTheory.Prod.snd Cᵒᵖ C ⋙ F)) ⋙ D.hom)) ∧
      ∃ e :
          ((((CategoryTheory.Prod.fst Cᵒᵖ C ⋙ F.op).prod'
              (CategoryTheory.Prod.snd Cᵒᵖ C ⋙ F)) ⋙ D.hom) ≅
            (((CategoryTheory.Prod.fst Cᵒᵖ C).prod'
              (CategoryTheory.Prod.snd Cᵒᵖ C ⋙ F)) ⋙ D.hom)),
        ∀ (K L : C), e.hom.app (Opposite.op K, L) =
          D.hom.map
            (show (Opposite.op (F.obj K), F.obj L) ⟶ (Opposite.op K, F.obj L) from
              ((η.app K).op, 𝟙 (F.obj L))) :=
  derivedHom_cechCompletion_aux A f

end DerivedHomCechCompletion

end



end
