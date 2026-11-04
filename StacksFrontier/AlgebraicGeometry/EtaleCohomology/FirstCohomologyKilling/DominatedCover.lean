module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FirstCohomologyKilling.FiniteEtaleCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.Curves.FiniteEtaleCoverConstantField
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleCofinality

/-!
# Killing cohomology classes by base changes of finite étale covers

Let `i : Z ⟶ Y` be a morphism of connected schemes which dominates finite étale covers
(`AlgebraicGeometry.DominatesFiniteEtale`), e.g. `X_k̄ ⟶ X` (the injectivity half of Tag 0BTX).
A cohomology class on `Z` which dies on some surjective finite étale cover of `Z` already dies on
the base change `W ×_Y Z` of a surjective finite étale cover `W` of `Y`. Consequently every class
of `H¹(Z, i⁻¹G)` dies on such a base change, for an abelian sheaf `G` on `Y` which becomes
constant with finite value on a surjective finite étale cover of `Y`.

## Main results

* `mapExactFunctor_comp_eq_zero_of_etaleCohomologyRestrictionMap`: if the restriction of a class
  along `a` dies under the inverse image along `b`, the class dies under the inverse image along
  `b ≫ a`.
* `exists_finite_etale_surjective_restriction_eq_zero_of_dominatesFiniteEtale`: a class dying on a
  surjective finite étale cover of `Z` dies on the base change of a surjective finite étale cover
  of `Y`.
* `exists_finite_etale_surjective_restriction_eq_zero_of_trivialization`: every class of
  `H¹(Z, i⁻¹G)` dies on the base change of a surjective finite étale cover of `Y`, for `G` which
  becomes constant with finite value on a surjective finite étale cover of `Y`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable {X Y Z : Scheme.{u}}

/-- **A class whose restriction dies on a cover dies under the composite.** If the restriction of
`x` along `a` dies under the inverse image along `b`, then `x` dies under the inverse image along
`b ≫ a`. This is the converse of
`Stacks.EtaleCohomology.mapExactFunctor_etaleCohomologyRestrictionMap_eq_zero`. -/
theorem mapExactFunctor_comp_eq_zero_of_etaleCohomologyRestrictionMap (a : Y ⟶ X) (b : Z ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) {q : ℕ} (x : Sheaf.H.{u + 1} F q)
    (h : (etaleCohomologyRestrictionMap.{u, 0, u + 1} a F q x).mapExactFunctor
      (etaleAbelianInverseImage.{u, 0} b) = 0) :
    x.mapExactFunctor (etaleAbelianInverseImage.{u, 0} (b ≫ a)) = 0 := by
  rw [etaleCohomologyRestrictionMap_apply.{u, 0, u + 1}, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀] at h
  rw [← mapExactFunctor_etaleAbelianInverseImage_comp_eq_zero_iff a b x]
  have h' := congrArg (fun y => (Ext.mk₀ ((etaleAbelianInverseImage.{u, 0} b).map
    ((etaleAbelianInverseImageConstantIso.{u, 0} a).app (AddCommGrpCat.of (ULift ℤ))).hom)).comp
      y (zero_add q)) h
  simpa [← Ext.comp_assoc_of_second_deg_zero, ← Functor.map_comp] using h'

/-- **A class dying on a surjective finite étale cover of `Z` dies on the base change of one of
`Y`**, for `i : Z ⟶ Y` a morphism of connected schemes dominating finite étale covers. -/
theorem exists_finite_etale_surjective_restriction_eq_zero_of_dominatesFiniteEtale
    [ConnectedSpace Z] [ConnectedSpace Y] (i : Z ⟶ Y) (hi : DominatesFiniteEtale i)
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) {q : ℕ} (θ : Sheaf.H.{u + 1} F q)
    {V : Scheme.{u}} (v : V ⟶ Z) [IsFinite v] [Etale v] [Surjective v]
    (hk : θ.mapExactFunctor (etaleAbelianInverseImage.{u, 0} v) = 0) :
    ∃ (W : Scheme.{u}) (π : W ⟶ Y), IsFinite π ∧ Etale π ∧ Surjective π ∧
      etaleCohomologyRestrictionMap.{u, 0, u + 1} (pullback.snd π i) F q θ = 0 := by
  obtain ⟨z⟩ : Nonempty Z := inferInstance
  let A₀ : FiniteEtaleOver Z := MorphismProperty.Over.mk ⊤ v ⟨inferInstance, inferInstance⟩
  have : Nonempty A₀.left := ⟨(v.surjective z).choose⟩
  obtain ⟨W, hW, ⟨m⟩⟩ := exists_hom_finiteEtaleBaseChange_of_dominatesFiniteEtale i hi
    (GeometricPoint.ofPoint Z z) A₀
  have : IsFinite W.hom := W.prop.1
  have : Etale W.hom := W.prop.2
  refine ⟨W.left, W.hom, inferInstance, inferInstance, ⟨surjective_of_finiteEtale W⟩, ?_⟩
  let b : (pullback W.hom i : Scheme.{u}) ⟶ V := m.left
  have hfac : pullback.snd W.hom i = b ≫ v := (MorphismProperty.Over.w m).symm
  have h₁ : θ.mapExactFunctor (etaleAbelianInverseImage.{u, 0} (b ≫ v)) = 0 := by
    refine (mapExactFunctor_etaleAbelianInverseImage_comp_eq_zero_iff v b θ).1 ?_
    rw [hk]
    exact Ext.mapExactFunctor_zero _ _ _ _
  have h₂ : θ.mapExactFunctor (etaleAbelianInverseImage.{u, 0} (pullback.snd W.hom i)) = 0 :=
    (Stacks.ExtFunctorial.mapExactFunctor_eq_zero_iff_of_iso
      (eqToIso (congrArg (fun k => etaleAbelianInverseImage.{u, 0} k) hfac)) θ).2 h₁
  rw [etaleCohomologyRestrictionMap_apply, h₂]
  exact Ext.comp_zero _ _ _ _ _

/-- **The degree-one effacement.** Let `i : Z ⟶ Y` be a morphism of connected schemes dominating
finite étale covers and `G` an abelian sheaf on `Y` whose inverse image to some surjective finite
étale `p : T ⟶ Y` is constant with finite value. Then every class of `H¹(Z, i⁻¹G)` dies on the
base change `W ×_Y Z` of some surjective finite étale `W ⟶ Y`. -/
theorem exists_finite_etale_surjective_restriction_eq_zero_of_trivialization
    [ConnectedSpace Z] [ConnectedSpace Y] (i : Z ⟶ Y) (hi : DominatesFiniteEtale i)
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) {T : Scheme.{u}} (p : T ⟶ Y)
    [IsFinite p] [Etale p] [Surjective p] (A : AddCommGrpCat.{u + 1}) [Finite A]
    (e : (etaleAbelianInverseImage.{u, 0} p).obj G ≅
      (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)
    (ξ : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} i).obj G) 1) :
    ∃ (W : Scheme.{u}) (π : W ⟶ Y), IsFinite π ∧ Etale π ∧ Surjective π ∧
      etaleCohomologyRestrictionMap.{u, 0, u + 1} (pullback.snd π i) _ 1 ξ = 0 := by
  let s := pullback.snd p i
  let e' : (etaleAbelianInverseImage.{u, 0} s).obj ((etaleAbelianInverseImage.{u, 0} i).obj G) ≅
      (constantSheaf (pullback p i).smallEtaleTopology AddCommGrpCat.{u + 1}).obj A :=
    ((etaleAbelianInverseImageCompIso'.{u, 0} s i (s ≫ i) rfl).app G).symm ≪≫
      (etaleAbelianInverseImageCompIso'.{u, 0} (pullback.fst p i) p (s ≫ i)
        pullback.condition.symm).app G ≪≫
      (etaleAbelianInverseImage.{u, 0} (pullback.fst p i)).mapIso e ≪≫
      (etaleAbelianInverseImageConstantIso.{u, 0} (pullback.fst p i)).app A
  let r := etaleCohomologyRestrictionMap.{u, 0, u + 1} s _ 1 ξ
  obtain ⟨V₀, hV₀f, hV₀s, hk⟩ :=
    exists_finite_etale_surjective_mapExactFunctor_eq_zero A (Sheaf.H.map e'.hom 1 r)
  have hr : r.mapExactFunctor (etaleAbelianInverseImage.{u, 0} V₀.hom) = 0 := by
    rw [Sheaf.H.map_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀] at hk
    have h' := congrArg (fun y => y.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, 0} V₀.hom).map
      e'.inv)) (add_zero 1)) hk
    simpa [← Functor.map_comp] using h'
  have hξ := mapExactFunctor_comp_eq_zero_of_etaleCohomologyRestrictionMap s V₀.hom _ ξ hr
  have : IsFinite V₀.hom := hV₀f
  have : Etale V₀.hom := V₀.prop
  have : Surjective V₀.hom := hV₀s
  exact exists_finite_etale_surjective_restriction_eq_zero_of_dominatesFiniteEtale i hi _ ξ
    (V₀.hom ≫ s) hξ

end Stacks.EtaleCohomology

end
