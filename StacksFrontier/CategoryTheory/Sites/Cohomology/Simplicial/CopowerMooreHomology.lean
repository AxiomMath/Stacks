module

public import StacksFrontier.AlgebraicTopology.SimplicialObject.CopowerProductSimplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.MooreComplexLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Copower.LocallyBijective
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso

/-!
# The Moore complex of a copower by a sum of representables

Let `C` be a site and `π : Δ × C ⥤ C` the projection. For an abelian presheaf `P` on `Δ × C`
and an object `X = (⦋m⦌, U)` of `Δ × C`, the copower `P ⊗ h_X`, `(⦋n⦌, V) ↦ ⊕_{(⦋n⦌, V) ⟶ X} P`,
has Moore complexes `V ↦ s((P ⊗ h_X)(⦋•⦌, V)) = s(P(⦋•⦌, V) × Δ[m] × Hom(V, U))`; since `Δ[m]` is
contractible, their homology is `V ↦ ⊕_{V ⟶ U} H_n(s(P(⦋•⦌, V)))`. Sheafification inverts the
copower by `h_U` of a morphism it inverts. So a morphism `θ : P ⟶ P'` whose Moore homology is
inverted by sheafification on `C` keeps this property after multiplication by a sum of
representables.

The sum `∐_i h_{X i}`, `X i = (x_i, U_i)`, is replaced by the explicit sigma presheaf
`S : z ↦ Σ_i Mor(z, X i)` (`sigmaYonedaIso`), which maps to `π^*T` for
`T : V ↦ Σ_i Mor(V, U_i)` by forgetting the simplicial coordinate. Over each `V` this map of
simplicial sets `⦋•⦌ ↦ Σ_i Mor(⦋•⦌, x_i) × Mor(V, U_i)` to the constant `T(V)` is a homotopy
equivalence, contracting each `Δ[x_i]` onto its last vertex, so `P ⊗ S ⟶ P ⊗ π^*T` is a homology
isomorphism on Moore complexes. The Moore complex of `P ⊗ π^*T` is the degreewise copower by `T`
of that of `P`, and the copower by `T` is exact, so it commutes with homology.

## Main definitions

* `Stacks.SimplicialModules.sigmaYoneda`: the explicit sum of representables on `Δ × C`.
* `Stacks.SimplicialModules.copowerFunctor`: the exact functor `F ↦ F ⊗ T` on abelian presheaves.

## Main results

* `Stacks.SimplicialModules.homotopyEquivalences_sigmaYonedaProj`: the fibres of `S ⟶ π^*T` are
  homotopy equivalences of simplicial sets.
* `Stacks.SimplicialModules.isIso_sheafify_homology_moore_copowerMap_snd`: the statement for the
  copower by `π^*T`, for any presheaf of sets `T` on `C`.
* `Stacks.SimplicialModules.isIso_sheafify_homology_moore_copowerMap`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.SimplicialModules

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- The complex of presheaves `V ↦ s(P(⦋•⦌, V))` of Moore complexes of an abelian presheaf on
`Δ × C`. -/
abbrev mooreComplex :
    ((SimplexCategory × C)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ ChainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℕ :=
  (projectionSituation J).pointMooreComplex (projectionCosimplicial (C := C))

/-- An exact functor `G` out of abelian presheaves commutes with the Moore homology: `G` of the
`n`-th homology of the Moore complex is the `n`-th homology of the alternating face map complex
of `G` applied to the simplicial object `V ↦ P(⦋•⦌, V)`. -/
private def mooreComplexHomologyCompIso {E : Type*} [Category* E] [Abelian E] (n : ℕ)
    (G : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ E) [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] :
    (mooreComplex J ⋙ HomologicalComplex.homologyFunctor _ _ n) ⋙ G ≅
      ((projectionSituation J).pointEvaluation (projectionCosimplicial (C := C)) ⋙
        (SimplicialObject.whiskering _ _).obj G) ⋙ AlgebraicTopology.alternatingFaceMapComplex _ ⋙
          HomologicalComplex.homologyFunctor _ _ n :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (mooreComplex J)
      (StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso G _ n).symm ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft
      ((projectionSituation J).pointEvaluation (projectionCosimplicial (C := C)))
      (AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso G))
      (HomologicalComplex.homologyFunctor _ _ n) ≪≫ Functor.associator _ _ _

/-! ### The sum of representables as an explicit presheaf of sets -/

section SigmaYoneda

variable {ι : Type u} (X : ι → SimplexCategory × C)

/-- The presheaf of sets `z ↦ ∐_i Mor(z, X i)` on `Δ × C`, as an explicit sigma type. -/
@[simps]
def sigmaYoneda : (SimplexCategory × C)ᵒᵖ ⥤ Type u where
  obj z := Σ i, (z.unop ⟶ X i)
  map f := TypeCat.ofHom fun g => ⟨g.1, f.unop ≫ g.2⟩
  map_id _ := by
    ext ⟨i, g⟩
    · rfl
    · exact heq_of_eq (Category.id_comp g)
  map_comp _ _ := by
    ext ⟨i, g⟩
    · rfl
    · exact heq_of_eq (Category.assoc _ _ g)

/-- The presheaf of sets `V ↦ ∐_i Mor(V, U_i)` on `C`, where `X i = (x_i, U_i)`. -/
@[simps]
def sigmaYonedaBase : Cᵒᵖ ⥤ Type u where
  obj V := Σ i, (V.unop ⟶ (X i).2)
  map f := TypeCat.ofHom fun g => ⟨g.1, f.unop ≫ g.2⟩
  map_id _ := by
    ext ⟨i, g⟩
    · rfl
    · exact heq_of_eq (Category.id_comp g)
  map_comp _ _ := by
    ext ⟨i, g⟩
    · rfl
    · exact heq_of_eq (Category.assoc _ _ g)

/-- Forgetting the simplicial coordinate, `(a, g) ↦ g`. -/
@[simps]
def sigmaYonedaProj :
    sigmaYoneda X ⟶ (CategoryTheory.Prod.snd SimplexCategory C).op ⋙ sigmaYonedaBase X where
  app _ := TypeCat.ofHom fun g => ⟨g.1, g.2.2⟩

/-- The inclusion of the `i`-th summand `Mor(-, X i)` into the sigma presheaf. -/
@[simps]
def sigmaYonedaInc (i : ι) : yoneda.obj (X i) ⟶ sigmaYoneda X where
  app _ := TypeCat.ofHom fun g => ⟨i, g⟩

/-- The explicit sigma presheaf is the coproduct of the representables. -/
def sigmaYonedaIso : sigmaYoneda X ≅ ∐ fun i => yoneda.obj (X i) where
  hom :=
    { app z := TypeCat.ofHom fun g => (Sigma.ι (fun i => yoneda.obj (X i)) g.1).app z g.2
      naturality z z' f := by
        ext ⟨i, g⟩
        exact NatTrans.naturality_apply (Sigma.ι (fun i => yoneda.obj (X i)) i) f g }
  inv := Sigma.desc (sigmaYonedaInc X)
  hom_inv_id := by
    ext z ⟨i, g⟩
    exact ConcreteCategory.congr_hom (NatTrans.congr_app
      (Sigma.ι_desc (f := fun i => yoneda.obj (X i)) (sigmaYonedaInc X) i) z) g
  inv_hom_id := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_desc_assoc, Category.comp_id]
    ext z g
    rfl

/-- The fibre of the sigma presheaf over `V`: the simplicial set
`⦋m⦌ ↦ ∐_i Mor(⦋m⦌, x_i) × Mor(V, U_i)`. -/
abbrev sigmaYonedaFibre (V : C) : SimplicialObject (Type u) :=
  (projectionCosimplicial.obj V).op ⋙ sigmaYoneda X

/-- The fibre over `V` of `snd ⋙ sigmaYonedaBase X`, constant with value `∐_i Mor(V, U_i)`. -/
abbrev sigmaYonedaBaseFibre (V : C) : SimplicialObject (Type u) :=
  (projectionCosimplicial.obj V).op ⋙ (CategoryTheory.Prod.snd SimplexCategory C).op ⋙
    sigmaYonedaBase X

/-- The section of the projection of the fibre over `V` given by the last vertices of the
simplices. -/
@[simps]
def sigmaYonedaSection (V : C) : sigmaYonedaBaseFibre X V ⟶ sigmaYonedaFibre X V where
  app _ := TypeCat.ofHom fun t => ⟨t.1, (SimplexCategory.const _ _ (Fin.last _), t.2)⟩

open Simplicial SSet.stdSimplex MonoidalCategory in
/-- The contraction of each simplex `Δ[x_i]` onto its last vertex, on the fibre over `V`. -/
def sigmaYonedaContraction (V : C) :
    (sigmaYonedaFibre X V : SSet.{u}) ⊗ Δ[1] ⟶ (sigmaYonedaFibre X V : SSet.{u}) where
  app _ := TypeCat.ofHom fun z => ⟨z.1.1, (SimplexCategory.Hom.mk
    ⟨fun k => if asOrderHom z.2 k = 0 then z.1.2.1.toOrderHom k else Fin.last _, fun a b hab => by
      dsimp only
      split_ifs with h₁ h₂ h₂
      · exact z.1.2.1.toOrderHom.monotone hab
      · exact Fin.le_last _
      · exact absurd (Fin.le_zero_iff.mp (((asOrderHom z.2).monotone hab).trans_eq h₂)) h₁
      · exact le_rfl⟩, z.1.2.2)⟩
  naturality _ _ _ := rfl

open Simplicial SSet.stdSimplex MonoidalCategory in
/-- The `k`-th vertex of the contracted simplex is the `k`-th vertex of the original simplex
where the `Δ[1]` coordinate is `0`, and the last vertex otherwise. -/
lemma sigmaYonedaContraction_app_apply (V : C) (m : SimplexCategoryᵒᵖ)
    (z : ((sigmaYonedaFibre X V : SSet.{u}) ⊗ Δ[1]).obj m) (k : Fin (m.unop.len + 1)) :
    ((sigmaYonedaContraction X V).app m z).2.1.toOrderHom k =
      if asOrderHom z.2 k = 0 then z.1.2.1.toOrderHom k else Fin.last _ :=
  rfl

open Simplicial SSet.stdSimplex MonoidalCategory in
/-- The contraction is a homotopy from the identity to the projection followed by the section. -/
def sigmaYonedaHomotopy (V : C) :
    SSet.Homotopy (𝟙 (sigmaYonedaFibre X V : SSet.{u}))
      (Functor.whiskerLeft (projectionCosimplicial.obj V).op (sigmaYonedaProj X) ≫
        sigmaYonedaSection X V) where
  h := sigmaYonedaContraction X V
  h₀ := by
    ext m ⟨i, a, g⟩
    refine Sigma.ext rfl (heq_of_eq (Prod.ext ?_ rfl))
    ext k : 3
    exact (sigmaYonedaContraction_app_apply X V m (SSet.ι₀.app m ⟨i, (a, g)⟩) k).trans
      (ite_eq_left rfl)
  h₁ := by
    ext m ⟨i, a, g⟩
    refine Sigma.ext rfl (heq_of_eq (Prod.ext ?_ rfl))
    ext k : 3
    exact (sigmaYonedaContraction_app_apply X V m (SSet.ι₁.app m ⟨i, (a, g)⟩) k).trans
      (ite_eq_right (show ¬ ((1 : Fin 2) = 0) by decide))
  rel := by
    ext n z
    exact z.1.2.elim

/-- **The projection of the fibre over `V` to `∐_i Mor(V, U_i)` is a homotopy equivalence**: the
last vertices give a section, and contracting each simplex `Δ[x_i]` onto its last vertex is a
homotopy from the identity to the composite the other way round. -/
theorem homotopyEquivalences_sigmaYonedaProj (V : C) :
    SimplicialObject.homotopyEquivalences (Type u)
      (Functor.whiskerLeft (projectionCosimplicial.obj V).op (sigmaYonedaProj X)) :=
  ⟨sigmaYonedaSection X V,
    (Relation.EqvGen.rel _ _ ⟨(sigmaYonedaHomotopy X V).toSimplicialObjectHomotopy⟩).symm, by
      rw [show sigmaYonedaSection X V ≫ _ = 𝟙 _ by ext; rfl]
      exact Relation.EqvGen.refl _⟩

/-- **Forgetting the simplicial coordinate of `Q ⊗ ∐_i h_{X i}` is a homology isomorphism on Moore
complexes**: after evaluation at `V` it is the product of the simplicial object `Q(⦋•⦌, V)` with a
homotopy equivalence of simplicial sets. -/
theorem isIso_homologyMap_moore_copowerMap_sigmaYonedaProj
    (Q : (SimplexCategory × C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      ((mooreComplex J).map (Functor.copowerMap (𝟙 Q) (sigmaYonedaProj X))) n) := by
  let φ := Functor.copowerMap (𝟙 Q) (sigmaYonedaProj X)
  change IsIso ((mooreComplex J ⋙ HomologicalComplex.homologyFunctor _ _ n).map φ)
  rw [NatTrans.isIso_iff_isIso_app]
  rintro ⟨V⟩
  change IsIso (((mooreComplex J ⋙ HomologicalComplex.homologyFunctor _ _ n) ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op V)).map φ)
  rw [NatIso.isIso_map_iff (mooreComplexHomologyCompIso J n _)]
  exact SimplicialObject.isInvertedBy_homologyFunctor_alternatingFaceMapComplex n _
    (SimplicialObject.homotopyEquivalences_copowerMap_id
      ((projectionCosimplicial.obj V).op ⋙ Q) (homotopyEquivalences_sigmaYonedaProj X V))

end SigmaYoneda

/-! ### The copower by a presheaf of sets as an exact functor -/

section CopowerFunctor

variable {D : Type*} [Category* D] (T : D ⥤ Type u)

/-- The functor `F ↦ F ⊗ T`, `d ↦ ⊕_{t ∈ T(d)} F(d)`, on abelian presheaves. -/
@[simps]
def copowerFunctor : (D ⥤ AddCommGrpCat.{u}) ⥤ (D ⥤ AddCommGrpCat.{u}) where
  obj F := F.copower T
  map η := Functor.copowerMap η (𝟙 T)
  map_id F := Functor.copowerMap_id F T
  map_comp η η' := by rw [Functor.copowerMap_comp, Category.comp_id]

/-- The functor `F ↦ F ⊗ T` is additive. -/
instance : (copowerFunctor T).Additive where
  map_add {F G η η'} := by
    change Functor.copowerMap (η + η') (𝟙 T) =
      Functor.copowerMap η (𝟙 T) + Functor.copowerMap η' (𝟙 T)
    ext d : 2
    refine Sigma.hom_ext _ _ fun t => ?_
    simp only [NatTrans.app_add, Preadditive.comp_add, Functor.ι_copowerMap_app,
      Preadditive.add_comp]

/-- After evaluation at `d`, the copower by `T` is the coproduct of `T(d)` copies. -/
def copowerFunctorEvaluationIso (d : D) :
    copowerFunctor T ⋙ (evaluation D AddCommGrpCat.{u}).obj d ≅
      (evaluation D AddCommGrpCat.{u}).obj d ⋙ Functor.const (Discrete (T.obj d)) ⋙ colim :=
  NatIso.ofComponents (fun F => (HasColimit.isoOfNatIso (Discrete.natIso fun _ => Iso.refl _) :
      (∐ fun _ : T.obj d => F.obj d) ≅
        colimit ((Functor.const (Discrete (T.obj d))).obj (F.obj d))))
    (fun {F F'} η => by
      refine colimit.hom_ext fun ⟨t⟩ => ?_
      change Sigma.ι (fun _ : T.obj d => F.obj d) t ≫ (Functor.copowerMap η (𝟙 T)).app d ≫
          (HasColimit.isoOfNatIso (Discrete.natIso fun _ => Iso.refl _) :
            (∐ fun _ : T.obj d => F'.obj d) ≅
              colimit ((Functor.const (Discrete (T.obj d))).obj (F'.obj d))).hom =
        Sigma.ι (fun _ : T.obj d => F.obj d) t ≫
          (HasColimit.isoOfNatIso (Discrete.natIso fun _ => Iso.refl _) :
            (∐ fun _ : T.obj d => F.obj d) ≅
              colimit ((Functor.const (Discrete (T.obj d))).obj (F.obj d))).hom ≫
            colimMap ((Functor.const (Discrete (T.obj d))).map (η.app d))
      rw [Functor.ι_copowerMap_app_assoc, HasColimit.isoOfNatIso_ι_hom,
        HasColimit.isoOfNatIso_ι_hom_assoc, ι_colimMap]
      simp)

/-- The functor `F ↦ F ⊗ T` preserves finite limits. -/
instance : PreservesFiniteLimits (copowerFunctor T) :=
  preservesFiniteLimits_of_evaluation _ fun d =>
    preservesFiniteLimits_of_natIso (copowerFunctorEvaluationIso T d).symm

/-- The functor `F ↦ F ⊗ T` preserves finite colimits. -/
instance : PreservesFiniteColimits (copowerFunctor T) :=
  preservesFiniteColimits_of_evaluation _ fun d =>
    preservesFiniteColimits_of_natIso (copowerFunctorEvaluationIso T d).symm

end CopowerFunctor

/-! ### The Moore complex of a copower by a presheaf on `C` -/

/-- The simplicial presheaf `V ↦ (P ⊗ π^*T)(⦋•⦌, V)` is the degreewise copower by `T` of the
simplicial presheaf `V ↦ P(⦋•⦌, V)`, naturally in `P`. -/
def pointEvaluationCopowerIso (T : Cᵒᵖ ⥤ Type u) :
    copowerFunctor ((CategoryTheory.Prod.snd SimplexCategory C).op ⋙ T) ⋙
        (projectionSituation J).pointEvaluation (projectionCosimplicial (C := C)) ≅
      (projectionSituation J).pointEvaluation (projectionCosimplicial (C := C)) ⋙
        (SimplicialObject.whiskering _ _).obj (copowerFunctor T) :=
  NatIso.ofComponents (fun P => NatIso.ofComponents (fun _ => Iso.refl _) (fun {k k'} φ => by
      refine (Category.comp_id _).trans (Eq.trans ?_ (Category.id_comp _).symm)
      ext V : 2
      refine Sigma.hom_ext _ _ fun t => ?_
      change Sigma.ι _ t ≫ (P.copower ((CategoryTheory.Prod.snd SimplexCategory C).op ⋙ T)).map
          ((((projectionSituation J).pointEvaluationShape projectionCosimplicial).map φ).app V) = _
      rw [Functor.copower_map, Sigma.ι_comp_map']
      change _ = Sigma.ι _ t ≫ (Functor.copowerMap
        (((projectionSituation J).pointEvaluation (projectionCosimplicial (C := C))).obj P |>.map φ)
          (𝟙 T)).app V
      rw [Functor.ι_copowerMap_app, show ((CategoryTheory.Prod.snd SimplexCategory C).op ⋙ T).map
        ((((projectionSituation J).pointEvaluationShape projectionCosimplicial).map φ).app V) =
          𝟙 _ from T.map_id _]
      rfl))
    (fun {P P'} θ => by
      ext k V : 3
      refine Sigma.hom_ext _ _ fun t => ?_
      simp only [NatTrans.comp_app]
      rfl)

/-- **Sheafification inverts the Moore homology of `θ ⊗ π^*T` when it inverts that of `θ`.** The
Moore complex of `P ⊗ π^*T` is the degreewise copower by `T` of that of `P`; the copower by `T`
is exact, so it commutes with homology, and it preserves the morphisms inverted by
sheafification. -/
theorem isIso_sheafify_homology_moore_copowerMap_snd
    {P P' : (SimplexCategory × C)ᵒᵖ ⥤ AddCommGrpCat.{u}} (θ : P ⟶ P') (n : ℕ)
    (h : IsIso ((presheafToSheaf J AddCommGrpCat.{u}).map
      (HomologicalComplex.homologyMap ((mooreComplex J).map θ) n)))
    (T : Cᵒᵖ ⥤ Type u) :
    IsIso ((presheafToSheaf J AddCommGrpCat.{u}).map
      (HomologicalComplex.homologyMap ((mooreComplex J).map
        (Functor.copowerMap θ (𝟙 ((CategoryTheory.Prod.snd SimplexCategory C).op ⋙ T)))) n)) := by
  let G := copowerFunctor T
  let H := HomologicalComplex.homologyFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.down ℕ) n
  let e : copowerFunctor ((CategoryTheory.Prod.snd SimplexCategory C).op ⋙ T) ⋙
      mooreComplex J ⋙ H ≅ (mooreComplex J ⋙ H) ⋙ G :=
    Functor.isoWhiskerRight (pointEvaluationCopowerIso J T)
      (AlgebraicTopology.alternatingFaceMapComplex _ ⋙ H) ≪≫
      (mooreComplexHomologyCompIso J n G).symm
  have h' : IsIso (((mooreComplex J ⋙ H) ⋙ G ⋙ presheafToSheaf J AddCommGrpCat.{u}).map θ) :=
    (J.W_iff _).1 (Stacks.Sites.Copower.W_copowerMap J _ ((J.W_iff _).2 h) T)
  exact (NatIso.isIso_map_iff (Functor.isoWhiskerRight e (presheafToSheaf J AddCommGrpCat.{u}) ≪≫
    Functor.associator _ _ _) θ).2 h'

/-- **Multiplying by a sum of representables preserves the morphisms whose Moore homology is
inverted by sheafification.** -/
theorem isIso_sheafify_homology_moore_copowerMap
    {P P' : (SimplexCategory × C)ᵒᵖ ⥤ AddCommGrpCat.{u}} (θ : P ⟶ P') (n : ℕ)
    (h : IsIso ((presheafToSheaf J AddCommGrpCat.{u}).map
      (HomologicalComplex.homologyMap ((mooreComplex J).map θ) n)))
    {ι : Type u} (X : ι → SimplexCategory × C) :
    IsIso ((presheafToSheaf J AddCommGrpCat.{u}).map
      (HomologicalComplex.homologyMap ((mooreComplex J).map
        (Functor.copowerMap θ (𝟙 (∐ fun i => yoneda.obj (X i))))) n)) := by
  let τ := (sigmaYonedaIso X).inv ≫ sigmaYonedaProj X
  let F := mooreComplex J ⋙ HomologicalComplex.homologyFunctor _ (ComplexShape.down ℕ) n ⋙
    presheafToSheaf J AddCommGrpCat.{u}
  have key : ∀ Q : (SimplexCategory × C)ᵒᵖ ⥤ AddCommGrpCat.{u},
      IsIso (F.map (Functor.copowerMap (𝟙 Q) τ)) := fun Q => by
    have : IsIso (Functor.copowerMap (𝟙 Q) (sigmaYonedaIso X).inv) :=
      ⟨Functor.copowerMap (𝟙 Q) (sigmaYonedaIso X).hom, by simp, by simp⟩
    have : IsIso (F.map (Functor.copowerMap (𝟙 Q) (sigmaYonedaProj X))) :=
      have := isIso_homologyMap_moore_copowerMap_sigmaYonedaProj J X Q n
      inferInstanceAs (IsIso ((presheafToSheaf J AddCommGrpCat.{u}).map
        (HomologicalComplex.homologyMap
          ((mooreComplex J).map (Functor.copowerMap (𝟙 Q) (sigmaYonedaProj X))) n)))
    rw [show Functor.copowerMap (𝟙 Q) τ = Functor.copowerMap (𝟙 Q) (sigmaYonedaIso X).inv ≫
      Functor.copowerMap (𝟙 Q) (sigmaYonedaProj X) by simp [τ], F.map_comp]
    infer_instance
  have h₁ : IsIso (F.map (Functor.copowerMap θ
      (𝟙 ((CategoryTheory.Prod.snd SimplexCategory C).op ⋙ sigmaYonedaBase X)))) :=
    isIso_sheafify_homology_moore_copowerMap_snd J θ n h _
  have hsq : Functor.copowerMap θ (𝟙 (∐ fun i => yoneda.obj (X i))) ≫
      Functor.copowerMap (𝟙 P') τ = Functor.copowerMap (𝟙 P) τ ≫
        Functor.copowerMap θ (𝟙 ((CategoryTheory.Prod.snd SimplexCategory C).op ⋙
          sigmaYonedaBase X)) := by
    simp
  have := key P
  have := key P'
  have : IsIso (F.map (Functor.copowerMap θ (𝟙 (∐ fun i => yoneda.obj (X i)))) ≫
      F.map (Functor.copowerMap (𝟙 P') τ)) := by
    rw [← F.map_comp, hsq, F.map_comp]
    infer_instance
  exact IsIso.of_isIso_comp_right (F.map _) (F.map (Functor.copowerMap (𝟙 P') τ))

end Stacks.SimplicialModules
