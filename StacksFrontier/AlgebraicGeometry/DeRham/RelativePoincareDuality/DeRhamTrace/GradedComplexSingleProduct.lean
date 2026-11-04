module

public import StacksFrontier.Algebra.Homology.TruncatedTotalProductConnecting
public import StacksFrontier.Algebra.Homology.SingleSinglePairingShift

/-!
# Products of graded pieces through a lax comparison

Let `G : C ⥤ C'` be an additive functor, `F`, `F'` bifunctors on `C` and `C'`, and
`λ_{X,Y} : F'(GX, GY) ⟶ G F(X, Y)` a family of maps. Let `K` be a cochain complex of `C'` with a
multiplication `m : Tot(F'(K, K)) ⟶ K` vanishing above degree `n`, whose restriction to the summand
`F'(K^a, K^b)`, `a + b = n`, is `λ` followed by `G` of a map `μ : F(Ω_a, Ω_b) ⟶ Ω_{a+b}`, through
identifications `K^a ≅ GΩ_a`, `K^b ≅ GΩ_b`. Then the product of the graded pieces
`Tot(F'(K^a[-a], K^b[-b])) ⟶ K` (`StacksDraft.StupidTruncation.gradedMul`) is, through those
identifications, any comparison `Tot(F'(G(Ω_a[-a]), G(Ω_b[-b]))) ⟶ G Tot(F(Ω_a[-a], Ω_b[-b]))`
given by `λ` on the summands, followed by `G` of the pairing `Ω_a[-a] ⊗ Ω_b[-b] ⟶ Ω_n[-n]`
induced by `μ` and by a map `G(Ω_n[-n]) ⟶ K` of the top degree. This is a step of the proof of
[Stacks, Tag 0G8K], for `G` the restriction of scalars along `f⁻¹𝒪_S ⟶ 𝒪_X`.

## Main results

* `StacksDraft.StupidTruncation.mapBifunctorMap_comp_comp_map_comp_eq_gradedMul`

## References

* [Stacks Project, Tag 0G8K](https://stacks.math.columbia.edu/tag/0G8K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace StacksDraft.StupidTruncation

variable {C C' : Type*} [Category* C] [Category* C'] [Preadditive C] [Preadditive C']
  [HasZeroObject C] [HasZeroObject C']
  (F : C ⥤ C ⥤ C) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K L : CochainComplex C ℤ), HasMapBifunctor K L F (ComplexShape.up ℤ)]
  (F' : C' ⥤ C' ⥤ C') [additive_F' : F'.Additive] [additive_F'_obj : ∀ X, (F'.obj X).Additive]
  [∀ (K L : CochainComplex C' ℤ), HasMapBifunctor K L F' (ComplexShape.up ℤ)]
  (G : C ⥤ C') [additive_G : G.Additive]
  (lax : ∀ X Y : C, (F'.obj (G.obj X)).obj (G.obj Y) ⟶ G.obj ((F.obj X).obj Y))

omit [Preadditive C] [Preadditive C'] [HasZeroObject C] [HasZeroObject C'] [F.Additive]
  [∀ (X : C), (F.obj X).Additive]
  [∀ (K L : CochainComplex C ℤ), HasMapBifunctor K L F (ComplexShape.up ℤ)] additive_F'
  additive_F'_obj [∀ (K L : CochainComplex C' ℤ), HasMapBifunctor K L F' (ComplexShape.up ℤ)]
  additive_G in
/-- Any family of maps `F'(GX, GY) ⟶ G F(X, Y)` commutes with the identifications of equal
objects. -/
theorem lax_comp_map_eqToHom {X X' Y Y' : C} (p : X = X') (q : Y = Y') :
    lax X Y ≫ G.map ((F.map (eqToHom p)).app Y ≫ (F.obj X').map (eqToHom q)) =
      (F'.map (G.map (eqToHom p))).app (G.obj Y) ≫ (F'.obj (G.obj X')).map (G.map (eqToHom q)) ≫
        lax X' Y' := by
  subst p q
  simp

omit [Preadditive C'] [HasZeroObject C'] [F.Additive] [∀ (X : C), (F.obj X).Additive]
  [∀ (K L : CochainComplex C ℤ), HasMapBifunctor K L F (ComplexShape.up ℤ)] additive_F'
  additive_F'_obj [∀ (K L : CochainComplex C' ℤ), HasMapBifunctor K L F' (ComplexShape.up ℤ)]
  additive_G in
/-- `lax_comp_map_eqToHom` for the identifications of the terms of single complexes. -/
theorem lax_comp_map_singleObjXSelf (M N : C) (a b : ℤ) :
    lax _ _ ≫ G.map ((F.map (singleObjXSelf (ComplexShape.up ℤ) a M).hom).app _) ≫
      G.map ((F.obj M).map (singleObjXSelf (ComplexShape.up ℤ) b N).hom) =
      (F'.map (G.map (singleObjXSelf (ComplexShape.up ℤ) a M).hom)).app _ ≫
        (F'.obj (G.obj M)).map (G.map (singleObjXSelf (ComplexShape.up ℤ) b N).hom) ≫
        lax M N := by
  simp only [singleObjXSelf, singleObjXIsoOfEq, eqToIso.hom]
  exact (congrArg (lax _ _ ≫ ·) (G.map_comp _ _)).symm.trans (lax_comp_map_eqToHom F F' G lax _ _)

/-- A comparison `Tot(F'(GK₁, GK₂)) ⟶ G Tot(F(K₁, K₂))` is given by `lax` on the summands: on
`F'(GK₁^i, GK₂^j)` it is `λ` followed by `G` of the inclusion of the summand `F(K₁^i, K₂^j)`. -/
def IsLaxOnSummands {K₁ K₂ : CochainComplex C ℤ}
    (cup : mapBifunctor ((G.mapHomologicalComplex _).obj K₁) ((G.mapHomologicalComplex _).obj K₂) F'
        (ComplexShape.up ℤ) ⟶
      (G.mapHomologicalComplex _).obj (mapBifunctor K₁ K₂ F (ComplexShape.up ℤ))) : Prop :=
  ∀ (i j k : ℤ) (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (i, j) = k),
    ιMapBifunctor _ _ F' (ComplexShape.up ℤ) i j k h ≫ cup.f k =
      lax _ _ ≫ G.map (ιMapBifunctor K₁ K₂ F (ComplexShape.up ℤ) i j k h)

/-- A multiplication `m : Tot(F'(K, K)) ⟶ K` is, on the summand `F'(K^a, K^b)` of degree
`n = a + b`, the map `λ` followed by `G μ`, through `α : K^a ≅ GΩ_a`, `β : K^b ≅ GΩ_b` and
`γ : GΩ_n ⟶ K^n`. -/
def IsLaxProductOnSummand (Ω : ℤ → C) (a b n : ℤ) (hpq : a + b = n)
    (μ : (F.obj (Ω a)).obj (Ω b) ⟶ Ω (a + b)) (K : CochainComplex C' ℤ)
    (mK : mapBifunctor K K F' (ComplexShape.up ℤ) ⟶ K) (α : K.X a ≅ G.obj (Ω a))
    (β : K.X b ≅ G.obj (Ω b)) (γ : G.obj (Ω n) ⟶ K.X n) : Prop :=
  ιMapBifunctor K K F' (ComplexShape.up ℤ) a b n hpq ≫ mK.f n =
    (F'.map α.hom).app _ ≫ (F'.obj _).map β.hom ≫ lax _ _ ≫
      G.map (μ ≫ eqToHom (congrArg Ω hpq)) ≫ γ

/-- **The product of the graded pieces through a lax comparison.** -/
theorem mapBifunctorMap_comp_comp_map_comp_eq_gradedMul (Ω : ℤ → C) (a b n : ℤ)
    (hpq : a + b = n) (μ : (F.obj (Ω a)).obj (Ω b) ⟶ Ω (a + b)) (K : CochainComplex C' ℤ)
    (mK : mapBifunctor K K F' (ComplexShape.up ℤ) ⟶ K) (hM : ∀ k, n < k → IsZero (K.X k))
    (α : K.X a ≅ G.obj (Ω a)) (β : K.X b ≅ G.obj (Ω b)) (γ : G.obj (Ω n) ⟶ K.X n)
    (hm : IsLaxProductOnSummand F F' G lax Ω a b n hpq μ K mK α β γ)
    (t : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((single C (ComplexShape.up ℤ) n).obj (Ω n)) ⟶ K)
    (ht : t.f n = G.map (singleObjXSelf (ComplexShape.up ℤ) n (Ω n)).hom ≫ γ)
    (cup : mapBifunctor
      ((G.mapHomologicalComplex _).obj ((single C (ComplexShape.up ℤ) a).obj (Ω a)))
      ((G.mapHomologicalComplex _).obj ((single C (ComplexShape.up ℤ) b).obj (Ω b))) F'
        (ComplexShape.up ℤ) ⟶
      (G.mapHomologicalComplex _).obj (mapBifunctor ((single C (ComplexShape.up ℤ) a).obj (Ω a))
        ((single C (ComplexShape.up ℤ) b).obj (Ω b)) F (ComplexShape.up ℤ)))
    (hc : IsLaxOnSummands F F' G lax cup) :
    mapBifunctorMap ((single C' (ComplexShape.up ℤ) a).map α.hom ≫
        (singleMapHomologicalComplex G (ComplexShape.up ℤ) a).inv.app (Ω a))
      ((single C' (ComplexShape.up ℤ) b).map β.hom ≫
        (singleMapHomologicalComplex G (ComplexShape.up ℤ) b).inv.app (Ω b)) F'
        (ComplexShape.up ℤ) ≫ cup ≫
      (G.mapHomologicalComplex _).map ((mapBifunctorSingleSingleIso F (Ω a) (Ω b) a b).hom ≫
        (single C (ComplexShape.up ℤ) (a + b)).map μ ≫
        eqToHom (congrArg (fun k => (single C (ComplexShape.up ℤ) k).obj (Ω k)) hpq)) ≫ t =
    gradedMul F' mK hM a b hpq := by
  unfold IsLaxProductOnSummand at hm
  unfold IsLaxOnSummands at hc
  subst hpq
  refine CochainComplex.mapBifunctor_single_single_hom_ext F' (K.X a) (K.X b) a b ?_
  rw [ι_gradedMul_f F' mK hM a b rfl (a + b) rfl, hm]
  simp only [comp_f, eqToHom_refl, Category.comp_id, Functor.mapHomologicalComplex_map_f,
    ι_mapBifunctorMap_assoc, ht, single_map_f_self, singleMapHomologicalComplex_inv_app_self,
    Category.assoc]
  dsimp only [Functor.comp_obj]
  rw [reassoc_of% (hc a b (a + b) rfl)]
  simp only [← G.map_comp_assoc, Category.assoc, ι_mapBifunctorSingleSingleIso_hom_f_assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% (lax_comp_map_singleObjXSelf F F' G lax (Ω a) (Ω b) a b)]
  simp only [NatTrans.comp_app, Category.assoc, NatTrans.naturality_assoc]
  dsimp only [Functor.mapHomologicalComplex_obj_X]
  rw [NatTrans.naturality_assoc, NatTrans.naturality_assoc, NatTrans.naturality_assoc]
  simp only [← NatTrans.comp_app_assoc, ← CategoryTheory.Functor.map_comp_assoc,
    ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    NatTrans.id_app, Category.id_comp]

end StacksDraft.StupidTruncation
