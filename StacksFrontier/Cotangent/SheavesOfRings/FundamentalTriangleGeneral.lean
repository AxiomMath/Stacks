module

public import StacksFrontier.Cotangent.SheavesOfRings.FundamentalTriangle
public import StacksFrontier.Cotangent.SheavesOfRings.ProductRingSummand
public import StacksFrontier.Cotangent.SheavesOfRings.SectionwiseFundamentalTriangle
public import StacksFrontier.Cotangent.SheavesOfRings.SquareFunctorialityComp
import StacksCore.Tactic.StacksAttribute

/-!
# The fundamental triangle of sheaves of rings

Let `A ⟶ B ⟶ D` be homomorphisms of sheaves of commutative rings on a site. This file proves
that the triangle

`L_{B/A} ⊗_B D ⟶ L_{D/A} ⟶ L_{D/B} ⟶ (L_{B/A} ⊗_B D)[1]`

of Tag 08SZ, whose first two arrows are the canonical maps
`CategoryTheory.Sheaf.towerCotangentBaseChange` and
`CategoryTheory.Sheaf.towerCotangentChangeOfBase`, is distinguished.

## Main results

* `CategoryTheory.Sheaf.exists_distTriang_towerCotangent`: **Tag 08SZ**.

## Implementation notes

The argument is the one of the source. The homomorphism `B ⟶ B × D`, `b ↦ (b, h b)`
(`CategoryTheory.Sheaf.prodGraph`), is injective on sections, and for such a tower the triangle
is `CategoryTheory.Sheaf.exists_distTriang_towerCotangent_of_injective`. The second summand
functor `Mod(B × D) ⥤ Mod(D)` (`CategoryTheory.Sheaf.prodSndSummand`) is exact and carries the
triangle of the tower `A ⟶ B ⟶ B × D` to the triangle of `A ⟶ B ⟶ D`: on the second and third
vertices this is the second component of Tag 08SY, and on the first it is the composite of two
extensions of scalars. The product `B × D` is written `prodObj J B D` in the code.

## References

* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ)
* [Stacks Project, Tag 08SY](https://stacks.math.columbia.edu/tag/08SY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite Simplicial

namespace CategoryTheory.Sheaf

universe u v w t

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B D : Sheaf J CommRingCat.{max u v w}} (g : A ⟶ B) (h : B ⟶ D)

/-! ## The graph `B ⟶ prodObj J B D` -/

/-- The homomorphism `B ⟶ prodObj J B D`, `b ↦ (b, h b)`. -/
abbrev prodGraph : B ⟶ prodObj J B D := prodRingHom J (𝟙 B) h

/-- The second component of the graph `b ↦ (b, h b)` is `h`. -/
lemma prodGraph_snd : prodGraph J h ≫ (prodSndHom J B D) = h := prodRingHom_snd J (𝟙 B) h

/-- The graph `B ⟶ prodObj J B D` is injective on sections: its first component is the identity. -/
lemma injective_prodGraph (U : Cᵒᵖ) : Function.Injective ((prodGraph J h).hom.app U).hom := by
  have key : ∀ z, ((prodFstHom J B D).hom.app U).hom
      (((prodGraph J h).hom.app U).hom z) = z := fun z =>
    congrArg (fun k : B ⟶ B => (k.hom.app U).hom z) (prodRingHom_fst J (𝟙 B) h)
  intro x y hxy
  rw [← key x, ← key y, hxy]

/-! ## The second summand functor on complexes -/

/-- The second summand functor, applied degreewise to complexes. -/
abbrev prodSndSummandComplex :
    CochainComplex (targetModules.{u, v, w} J (prodObj J B D)) ℤ ⥤
      CochainComplex (targetModules.{u, v, w} J D) ℤ :=
  (prodSndSummand.{u, v, w} J (B := B) (D := D)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The counit of `prodSndSummand ⊣ prodRestrictSnd`, applied degreewise to a complex. -/
abbrev prodSndSummandCounitComplex (X : CochainComplex (targetModules.{u, v, w} J D) ℤ) :
    (prodSndSummandComplex.{u, v, w} J (B := B)).obj
        (((prodRestrictSnd J B D).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ⟶ X :=
  (NatTrans.mapHomologicalComplex (prodSndSummandAdjunction.{u, v, w} J (B := B) (D := D)).counit
    (ComplexShape.up ℤ)).app X

/-- The counit of the second summand functor is an isomorphism of complexes. -/
instance (X : CochainComplex (targetModules.{u, v, w} J D) ℤ) :
    IsIso (prodSndSummandCounitComplex.{u, v, w} J (B := B) X) :=
  have : ∀ n, IsIso ((prodSndSummandCounitComplex.{u, v, w} J (B := B) X).f n) := fun n =>
    inferInstanceAs (IsIso ((prodSndSummandAdjunction.{u, v, w} J (B := B) (D := D)).counit.app
      (X.X n)))
  HomologicalComplex.Hom.isIso_of_components _

/-! ## The second summand of the cotangent complex of a product -/

section ProdSnd

variable {A' : Sheaf J CommRingCat.{max u v w}}

/-- The comparison `e_D L_{prodObj J B D/A'} ⟶ L_{D/A'}`: the second summand of the map of
cotangent complexes induced by the second projection. -/
def prodSndCotangentComparison (f₀ : A' ⟶ prodObj J B D) (g' : A' ⟶ D)
    (hsq : f₀ ≫ (prodSndHom J B D) = 𝟙 A' ≫ g') :
    (prodSndSummandComplex.{u, v, w} J (B := B)).obj (cotangentComplex.{u, v, w} J f₀) ⟶
      cotangentComplex.{u, v, w} J g' :=
  (prodSndSummandComplex.{u, v, w} J (B := B)).map
      (squareCotangentComplexMap (resolutionSquareMap.{u, v, w} J (𝟙 A') (prodSndHom J B D) hsq)) ≫
    prodSndSummandCounitComplex.{u, v, w} J (B := B) _

/-- The second summand functor, being exact, preserves homology. -/
instance : (prodSndSummand.{u, v, w} J (B := B) (D := D)).PreservesHomology :=
  Functor.preservesHomologyOfExact _

/-- The second summand kills every map of complexes of `prodObj J B D`-modules factoring through a
complex of `B`-modules read over `prodObj J B D`. -/
lemma prodSndSummandComplex_map_eq_zero
    {X Y : CochainComplex (targetModules.{u, v, w} J (prodObj J B D)) ℤ}
    (Z : CochainComplex (targetModules.{u, v, w} J B) ℤ)
    (α : X ⟶ ((prodRestrictFst J B D).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)
    (β : ((prodRestrictFst J B D).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z ⟶ Y) :
    (prodSndSummandComplex.{u, v, w} J (B := B) (D := D)).map (α ≫ β) = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  rw [Functor.mapHomologicalComplex_map_f, HomologicalComplex.comp_f, Functor.map_comp,
    (isZero_prodSndSummand_prodRestrictFst.{u, v, w} J (Z.X n)).eq_of_tgt
      ((prodSndSummand.{u, v, w} J).map (α.f n)) 0, zero_comp]
  rfl

/-- **The second component of Tag 08SY**: for `f₀ = (g₁, g')`, the comparison
`e_D L_{prodObj J B D/A'} ⟶ L_{D/A'}` is a quasi-isomorphism. -/
theorem quasiIso_prodSndCotangentComparison (f₀ : A' ⟶ prodObj J B D) (g₁ : A' ⟶ B) (g' : A' ⟶ D)
    (hf₀ : f₀ = prodRingHom J g₁ g') (hsq : f₀ ≫ (prodSndHom J B D) = 𝟙 A' ≫ g') :
    QuasiIso (prodSndCotangentComparison.{u, v, w} J f₀ g' hsq) := by
  subst hf₀
  have hbp : ∀ (P : Sheaf J CommRingCat.{max u v w})
      (X Y : CochainComplex (targetModules.{u, v, w} J P) ℤ), HasBinaryBiproduct X Y :=
    fun _ _ _ => inferInstance
  have := hbp (prodObj J B D) (prodCotangentSummandFst J g₁ (B' := D))
    (prodCotangentSummandSnd J g' (B := B))
  let E := prodSndSummandComplex.{u, v, w} J (B := B) (D := D)
  have := quasiIso_prodCotangentComparison J g₁ g'
  have hq : QuasiIso (E.map (prodCotangentComparison J g₁ g')) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology _ _
  have hsnd : IsIso (E.map (prodCotangentSumSnd J g₁ g')) := by
    refine ⟨E.map biprod.inr, ?_, ?_⟩
    · have h₀ := biprod.total (X := prodCotangentSummandFst J g₁ (B' := D))
        (Y := prodCotangentSummandSnd J g' (B := B))
      have h₁ : E.map (biprod.fst ≫ biprod.inl :
          prodCotangentSum J g₁ g' ⟶ prodCotangentSum J g₁ g') = 0 :=
        prodSndSummandComplex_map_eq_zero J _ _ _
      rw [← E.map_comp, ← E.map_id, ← h₀, E.map_add, h₁, zero_add]
    · rw [← E.map_comp, biprod.inr_snd, E.map_id]
  have hcomp : prodSndCotangentComparison.{u, v, w} J (prodRingHom J g₁ g') g' hsq =
      E.map (prodCotangentComparison J g₁ g') ≫ E.map (prodCotangentSumSnd J g₁ g') ≫
        prodSndSummandCounitComplex.{u, v, w} J (B := B) _ := by
    rw [← Category.assoc, ← E.map_comp, prodCotangentComparison_snd]
    rfl
  rw [hcomp]
  infer_instance

end ProdSnd

/-! ## The second arrow -/

section SecondArrow

/-- The square `(𝟙 A, (prodSndHom J B D))` from `g ≫ (b ↦ (b, h b))` to `g ≫ h`. -/
lemma prodGraph_square_base : (g ≫ prodGraph J h) ≫ (prodSndHom J B D) = 𝟙 A ≫ (g ≫ h) := by
  rw [Category.assoc, prodGraph_snd, Category.id_comp]

/-- The square `(𝟙 B, (prodSndHom J B D))` from `b ↦ (b, h b)` to `h`. -/
lemma prodGraph_square_top : prodGraph J h ≫ (prodSndHom J B D) = 𝟙 B ≫ h := by
  rw [prodGraph_snd, Category.id_comp]

attribute [local instance] moduleOfSections

/-- The degree-`n` component of the change of base ring of a tower `A ⟶ B ⟶ D'`, with the
restriction of scalars along the identity of `D'` removed from its target. -/
def changeOfBaseTerm {D' : Sheaf J CommRingCat.{max u v w}} (h' : B ⟶ D') (n : SimplexCategoryᵒᵖ) :
    (cotangentSimplicialModule.{u, v, w} J (g ≫ h')).object.obj n ⟶
      (cotangentSimplicialModule.{u, v, w} J h').object.obj n :=
  squareCotangentTermMap (towerFunctorialitySquare.{u, v, w} J g h') n

/-- The degree-`n` component of the map `L_{B ⨯ D/A'} ⟶ L_{D/A'}` induced by the second
projection. -/
def prodSndTerm {A' : Sheaf J CommRingCat.{max u v w}} (f₀ : A' ⟶ prodObj J B D) (g' : A' ⟶ D)
    (hsq : f₀ ≫ prodSndHom J B D = 𝟙 A' ≫ g') (n : SimplexCategoryᵒᵖ) :
    (cotangentSimplicialModule.{u, v, w} J f₀).object.obj n ⟶
      (prodRestrictSnd J B D).obj ((cotangentSimplicialModule.{u, v, w} J g').object.obj n) :=
  squareCotangentTermMap (resolutionSquareMap.{u, v, w} J (𝟙 A') (prodSndHom J B D) hsq) n

/-- In each simplicial degree, the change of base ring of the tower `A ⟶ B ⟶ B ⨯ D` followed by
the second projection is the second projection followed by the change of base ring of the tower
`A ⟶ B ⟶ D`. -/
lemma changeOfBaseTerm_prodSndTerm (n : SimplexCategoryᵒᵖ) :
    changeOfBaseTerm J g (prodGraph J h) n ≫
        prodSndTerm J (prodGraph J h) h (prodGraph_square_top J h) n =
      prodSndTerm J (g ≫ prodGraph J h) (g ≫ h) (prodGraph_square_base J g h) n ≫
        (prodRestrictSnd J B D).map (changeOfBaseTerm J g h n) := by
  refine ((cotangentSimplicialModule.{u, v, w} J (g ≫ prodGraph J h)).derivationEquiv n
    ((prodRestrictSnd J B D).obj
      ((cotangentSimplicialModule.{u, v, w} J h).object.obj n))).injective
    (PresheafOfModulesOfCommRing.Derivation.ext (funext fun U => AddMonoidHom.ext fun x => ?_))
  have hl := squareCotangentTermMap_comp_d
    (sq₁ := towerFunctorialitySquare.{u, v, w} J g (prodGraph J h))
    (sq₂ := resolutionSquareMap.{u, v, w} J (𝟙 B) (prodSndHom J B D) (prodGraph_square_top J h))
    (n := n) (U := U) (x := x)
  have hr := squareCotangentTermMap_comp_d
    (sq₁ := resolutionSquareMap.{u, v, w} J (𝟙 A) (prodSndHom J B D)
      (prodGraph_square_base J g h))
    (sq₂ := towerFunctorialitySquare.{u, v, w} J g h) (n := n) (U := U) (x := x)
  refine hl.trans (Eq.trans ?_ hr.symm)
  have h₁ := resolutionSquareMap_resolution_comp J (f := g ≫ prodGraph J h) (f' := prodGraph J h)
    (f'' := h) g (𝟙 (prodObj J B D)) (Category.comp_id _) (𝟙 B) (prodSndHom J B D)
    (prodGraph_square_top J h) (Category.comp_id g) (Category.id_comp _)
    (by rw [Category.assoc, prodGraph_snd]) n
  have h₂ := resolutionSquareMap_resolution_comp J (f := g ≫ prodGraph J h) (f' := g ≫ h)
    (f'' := h) (𝟙 A) (prodSndHom J B D) (prodGraph_square_base J g h) g (𝟙 D)
    (Category.comp_id _) (Category.id_comp g) (Category.comp_id _)
    (by rw [Category.assoc, prodGraph_snd]) n
  have := congrArg (fun k : resolutionTerm.{u, v, w} J (g ≫ prodGraph J h) n ⟶
      resolutionTerm.{u, v, w} J h n => k.hom.app U x) (h₁.trans h₂.symm)
  exact congrArg (fun z => ((cotangentSimplicialModule.{u, v, w} J h).universalDerivation n).d z)
    this

/-- The degreewise second-arrow square, after the second summand functor and the counit. -/
@[reassoc]
lemma prodSndSummand_changeOfBase_term (n : SimplexCategoryᵒᵖ) :
    (prodSndSummand.{u, v, w} J (B := B) (D := D)).map (changeOfBaseTerm J g (prodGraph J h) n) ≫
      (prodSndSummand.{u, v, w} J (B := B) (D := D)).map
          (prodSndTerm J (prodGraph J h) h (prodGraph_square_top J h) n) ≫
        (prodSndSummandAdjunction.{u, v, w} J (B := B) (D := D)).counit.app
          ((cotangentSimplicialModule.{u, v, w} J h).object.obj n) =
    (prodSndSummand.{u, v, w} J (B := B) (D := D)).map
          (prodSndTerm J (g ≫ prodGraph J h) (g ≫ h) (prodGraph_square_base J g h) n) ≫
      (prodSndSummandAdjunction.{u, v, w} J (B := B) (D := D)).counit.app
          ((cotangentSimplicialModule.{u, v, w} J (g ≫ h)).object.obj n) ≫
        changeOfBaseTerm J g h n := by
  have e₂ := congrArg ((prodSndSummandAdjunction.{u, v, w} J (B := B) (D := D)).homEquiv _ _).symm
    (changeOfBaseTerm_prodSndTerm J g h n)
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_naturality_right_symm,
    Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc, Category.assoc] at e₂
  exact e₂

/-- In cohomological degree `-n` the change of base ring is its degreewise map. -/
lemma towerCotangentChangeOfBase_f' {D' : Sheaf J CommRingCat.{max u v w}} (h' : B ⟶ D')
    (n : ℕ) :
    (towerCotangentChangeOfBase.{u, v, w} J g h').f (-(n : ℤ)) =
      (cotangentComplex_degreeIso.{u, v, w} J (g ≫ h') n).hom ≫
        changeOfBaseTerm J g h' (op ⦋n⦌) ≫ (cotangentComplex_degreeIso.{u, v, w} J h' n).inv :=
  squareCotangentComplexMap_f _ n

/-- In cohomological degree `-n` the comparison `e_D L_{B ⨯ D/A'} ⟶ L_{D/A'}` is the second
summand of the degreewise map, followed by the counit. -/
lemma prodSndCotangentComparison_f {A' : Sheaf J CommRingCat.{max u v w}}
    (f₀ : A' ⟶ prodObj J B D) (g' : A' ⟶ D) (hsq : f₀ ≫ prodSndHom J B D = 𝟙 A' ≫ g') (n : ℕ) :
    (prodSndCotangentComparison.{u, v, w} J f₀ g' hsq).f (-(n : ℤ)) =
      (prodSndSummand.{u, v, w} J (B := B) (D := D)).map
          (cotangentComplex_degreeIso.{u, v, w} J f₀ n).hom ≫
        (prodSndSummand.{u, v, w} J (B := B) (D := D)).map (prodSndTerm J f₀ g' hsq (op ⦋n⦌)) ≫
          (prodSndSummandAdjunction.{u, v, w} J (B := B) (D := D)).counit.app
            ((cotangentSimplicialModule.{u, v, w} J g').object.obj (op ⦋n⦌)) ≫
            (cotangentComplex_degreeIso.{u, v, w} J g' n).inv := by
  have hc := (prodSndSummandAdjunction.{u, v, w} J (B := B) (D := D)).counit.naturality
    (cotangentComplex_degreeIso.{u, v, w} J g' n).inv
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hc
  rw [prodSndCotangentComparison, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    squareCotangentComplexMap_f, Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc, NatTrans.mapHomologicalComplex_app_f]
  rw [← hc]
  rfl

/-- Maps of cochain complexes out of a complex vanishing in positive degrees agree when they agree
in degrees `-n`, `n : ℕ`. -/
private theorem hom_ext_of_nonpos {M : Type*} [Category M] [Limits.HasZeroMorphisms M]
    (X Y : CochainComplex M ℤ) (f g : X ⟶ Y) (hX : ∀ i : ℤ, 0 < i → IsZero (X.X i))
    (h : ∀ n : ℕ, f.f (-(n : ℤ)) = g.f (-(n : ℤ))) : f = g := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  by_cases hi : 0 < i
  · exact (hX i hi).eq_of_src _ _
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = -(n : ℤ) := ⟨(-i).toNat, by omega⟩
  exact h n

/-- **The second arrows of the two towers correspond**: the second summand of the change of base
ring of `A ⟶ B ⟶ B ⨯ D` is the change of base ring of `A ⟶ B ⟶ D`, through the two
comparisons of Tag 08SY. -/
theorem prodSndCotangentComparison_changeOfBase :
    (prodSndSummandComplex.{u, v, w} J (B := B) (D := D)).map
        (towerCotangentChangeOfBase.{u, v, w} J g (prodGraph J h)) ≫
      prodSndCotangentComparison.{u, v, w} J (prodGraph J h) h (prodGraph_square_top J h) =
    prodSndCotangentComparison.{u, v, w} J (g ≫ prodGraph J h) (g ≫ h)
        (prodGraph_square_base J g h) ≫
      towerCotangentChangeOfBase.{u, v, w} J g h := by
  refine hom_ext_of_nonpos _ _ _ _ (fun i hi => ((prodSndSummand.{u, v, w} J (B := B)
    (D := D)).map_isZero (cotangentComplex_isZero_pos J _ i hi))) fun n => ?_
  have l₁ := towerCotangentChangeOfBase_f' J g (prodGraph J h) n
  have l₂ := towerCotangentChangeOfBase_f' J g h n
  have l₃ := prodSndCotangentComparison_f J (prodGraph J h) h (prodGraph_square_top J h) n
  have l₄ := prodSndCotangentComparison_f J (g ≫ prodGraph J h) (g ≫ h)
    (prodGraph_square_base J g h) n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    l₁, l₂, l₃, l₄]
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id_map_assoc, Iso.inv_hom_id_assoc]
  rw [prodSndSummand_changeOfBase_term_assoc]

end SecondArrow

/-! ## The first arrow -/

section FirstArrow

attribute [local instance] moduleOfSections

/-- The second component of `(b, h b)` is `h b`. -/
lemma prodSndApp_prodGraph (U : Cᵒᵖ)
    (b : (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj.obj U) :
    prodSndApp J U (((squareTargetRing.{u, v, w} J (prodGraph J h)).hom.app U).hom b) =
      ((squareTargetRing.{u, v, w} J h).hom.app U).hom b :=
  congrArg (fun k : B ⟶ D => (k.hom.app U).hom b) (prodGraph_snd J h)

/-- The identity on sections, from `N` read over `B` along `b ↦ (b, h b)` and the second
projection to `N` read over `B` along `h`. -/
def prodGraphRestrictHom (N : targetModules.{u, v, w} J D) :
    (squareRestrict.{u, v, w} J (prodGraph J h)).obj ((prodRestrictSnd J B D).obj N) ⟶
      (squareRestrict.{u, v, w} J h).obj N :=
  ⟨{ app := fun U => ConcreteCategory.ofHom (C := ModuleCat _)
        (X := ((squareRestrict.{u, v, w} J (prodGraph J h)).obj
          ((prodRestrictSnd J B D).obj N)).val.obj U)
        (Y := ((squareRestrict.{u, v, w} J h).obj N).val.obj U)
        { toFun := fun x => (x : N.val.obj U)
          map_add' := fun _ _ => rfl
          map_smul' := fun b x => by
            change prodSndApp J U (((squareTargetRing.{u, v, w} J (prodGraph J h)).hom.app
              U).hom b) • (show N.val.obj U from x) = _
            rw [prodSndApp_prodGraph]
            rfl }
     naturality := fun _ => rfl }⟩

/-- The inverse of `CategoryTheory.Sheaf.prodGraphRestrictHom`. -/
def prodGraphRestrictInv (N : targetModules.{u, v, w} J D) :
    (squareRestrict.{u, v, w} J h).obj N ⟶
      (squareRestrict.{u, v, w} J (prodGraph J h)).obj ((prodRestrictSnd J B D).obj N) :=
  ⟨{ app := fun U => ConcreteCategory.ofHom (C := ModuleCat _)
        (X := ((squareRestrict.{u, v, w} J h).obj N).val.obj U)
        (Y := ((squareRestrict.{u, v, w} J (prodGraph J h)).obj
          ((prodRestrictSnd J B D).obj N)).val.obj U)
        { toFun := fun x => (x : N.val.obj U)
          map_add' := fun _ _ => rfl
          map_smul' := fun b x => by
            change _ = prodSndApp J U (((squareTargetRing.{u, v, w} J
              (prodGraph J h)).hom.app U).hom b) • (show N.val.obj U from x)
            rw [prodSndApp_prodGraph]
            rfl }
     naturality := fun _ => rfl }⟩

/-- Restricting along the second projection and then along `b ↦ (b, h b)` is restricting along
`h`: the identity on sections. -/
def prodGraphRestrictIso :
    prodRestrictSnd J B D ⋙ squareRestrict.{u, v, w} J (prodGraph J h) ≅
      squareRestrict.{u, v, w} J h :=
  NatIso.ofComponents (fun N =>
    { hom := prodGraphRestrictHom J h N
      inv := prodGraphRestrictInv J h N
      hom_inv_id := rfl
      inv_hom_id := rfl }) (fun _ => by ext; rfl)

/-- `- ⊗_B (B ⨯ D)` followed by the second summand, as a left adjoint of restriction along `h`. -/
def prodGraphSummandAdjunction :
    towerExtendScalars.{u, v, w} J (prodGraph J h) ⋙ prodSndSummand.{u, v, w} J (B := B) (D := D) ⊣
      squareRestrict.{u, v, w} J h :=
  ((towerExtendRestrictAdjunction.{u, v, w} J (prodGraph J h)).comp
    (prodSndSummandAdjunction.{u, v, w} J (B := B) (D := D))).ofNatIsoRight
      (prodGraphRestrictIso J h)

/-- **`(- ⊗_B (B ⨯ D))` followed by the second summand is `- ⊗_B D`.** -/
def prodGraphSummandIso :
    towerExtendScalars.{u, v, w} J (prodGraph J h) ⋙ prodSndSummand.{u, v, w} J (B := B) (D := D) ≅
      towerExtendScalars.{u, v, w} J h :=
  Adjunction.leftAdjointUniq (prodGraphSummandAdjunction J h)
    (towerExtendRestrictAdjunction.{u, v, w} J h)

/-- In each simplicial degree, the base change along `b ↦ (b, h b)` followed by the second
projection and the identification of the two restrictions is the base change along `h`. -/
lemma squareCotangentTermMap_prodGraph_prodSndTerm (n : SimplexCategoryᵒᵖ) :
    squareCotangentTermMap (towerBaseChangeSquare.{u, v, w} J g (prodGraph J h)) n ≫
        (squareRestrict.{u, v, w} J (prodGraph J h)).map
          (prodSndTerm J (g ≫ prodGraph J h) (g ≫ h) (prodGraph_square_base J g h) n) ≫
        (prodGraphRestrictIso J h).hom.app _ =
      squareCotangentTermMap (towerBaseChangeSquare.{u, v, w} J g h) n := by
  refine squareCotangentTermMap_unique _ n _ fun U x => ?_
  have hn := PresheafOfModulesOfCommRing.Derivation.congr_d (X := U)
    ((cotangentSimplicialModule.{u, v, w} J g).naturality n
      (squareCotangentTermMap (towerBaseChangeSquare.{u, v, w} J g (prodGraph J h)) n ≫
        (squareRestrict.{u, v, w} J (prodGraph J h)).map
          (prodSndTerm J (g ≫ prodGraph J h) (g ≫ h) (prodGraph_square_base J g h) n))
      ((prodGraphRestrictIso J h).hom.app _)) x
  refine hn.trans ?_
  have hl := squareCotangentTermMap_comp_d
    (sq₁ := towerBaseChangeSquare.{u, v, w} J g (prodGraph J h))
    (sq₂ := resolutionSquareMap.{u, v, w} J (𝟙 A) (prodSndHom J B D)
      (prodGraph_square_base J g h)) (n := n) (U := U) (x := x)
  refine hl.trans ?_
  have h₁ := resolutionSquareMap_resolution_comp J (f := g) (f' := g ≫ prodGraph J h)
    (f'' := g ≫ h) (𝟙 A) (prodGraph J h) (Category.id_comp _).symm (𝟙 A) (prodSndHom J B D)
    (prodGraph_square_base J g h) (Category.id_comp _) (prodGraph_snd J h)
    (Category.id_comp _).symm n
  have := congrArg (fun k : resolutionTerm.{u, v, w} J g n ⟶
      resolutionTerm.{u, v, w} J (g ≫ h) n => k.hom.app U x) h₁
  exact congrArg (fun z => ((cotangentSimplicialModule.{u, v, w} J (g ≫ h)).universalDerivation
    n).d z) this

/-- **The first arrows of the two towers correspond**, in each simplicial degree: the second
summand of the transposed base change along `b ↦ (b, h b)`, followed by the second
projection, is the transposed base change along `h` through the identification
`(- ⊗_B (B ⨯ D))_D = - ⊗_B D`. -/
@[reassoc]
lemma prodSndSummand_baseChange_term (n : SimplexCategoryᵒᵖ) :
    (prodSndSummand.{u, v, w} J (B := B) (D := D)).map
        ((baseChangeSimplicialMap.{u, v, w} J g (prodGraph J h)).app n) ≫
      (prodSndSummand.{u, v, w} J (B := B) (D := D)).map
          (prodSndTerm J (g ≫ prodGraph J h) (g ≫ h) (prodGraph_square_base J g h) n) ≫
        (prodSndSummandAdjunction.{u, v, w} J (B := B) (D := D)).counit.app
          ((cotangentSimplicialModule.{u, v, w} J (g ≫ h)).object.obj n) =
    (prodGraphSummandIso J h).hom.app ((cotangentSimplicialModule.{u, v, w} J g).object.obj n) ≫
      (baseChangeSimplicialMap.{u, v, w} J g h).app n := by
  have hR : (prodGraphSummandAdjunction J h).homEquiv _ _
      ((prodGraphSummandIso J h).hom.app ((cotangentSimplicialModule.{u, v, w} J g).object.obj n) ≫
        (baseChangeSimplicialMap.{u, v, w} J g h).app n) =
      squareCotangentTermMap (towerBaseChangeSquare.{u, v, w} J g h) n := by
    rw [Adjunction.homEquiv_naturality_right, prodGraphSummandIso,
      Adjunction.homEquiv_leftAdjointUniq_hom_app, ← Adjunction.homEquiv_unit,
      baseChangeSimplicialMap_app, Equiv.apply_symm_apply]
  have hL : (prodGraphSummandAdjunction J h).homEquiv _ _
      ((prodSndSummand.{u, v, w} J (B := B) (D := D)).map
          ((baseChangeSimplicialMap.{u, v, w} J g (prodGraph J h)).app n) ≫
        (prodSndSummand.{u, v, w} J (B := B) (D := D)).map
            (prodSndTerm J (g ≫ prodGraph J h) (g ≫ h) (prodGraph_square_base J g h) n) ≫
          (prodSndSummandAdjunction.{u, v, w} J (B := B) (D := D)).counit.app
            ((cotangentSimplicialModule.{u, v, w} J (g ≫ h)).object.obj n)) =
      squareCotangentTermMap (towerBaseChangeSquare.{u, v, w} J g h) n := by
    rw [prodGraphSummandAdjunction, Adjunction.homEquiv_ofNatIsoRight_apply,
      Adjunction.comp_homEquiv]
    dsimp only [Equiv.trans_apply, Functor.id_obj]
    rw [← Functor.map_comp_assoc, ← Adjunction.homEquiv_counit, Equiv.apply_symm_apply,
      Adjunction.homEquiv_naturality_right, baseChangeSimplicialMap_app, Equiv.apply_symm_apply,
      Category.assoc]
    exact squareCotangentTermMap_prodGraph_prodSndTerm J g h n
  exact ((prodGraphSummandAdjunction J h).homEquiv _ _).injective (hL.trans hR.symm)

/-- **The first vertices of the two towers correspond**: the second summand of
`L_{B/A} ⊗_B (B ⨯ D)` is `L_{B/A} ⊗_B D`, both base changes being taken degreewise. -/
def prodGraphBaseChangedIso :
    (prodSndSummandComplex.{u, v, w} J (B := B) (D := D)).obj
        (baseChangedCotangentComplex.{u, v, w} J g (prodGraph J h)) ≅
      baseChangedCotangentComplex.{u, v, w} J g h :=
  (HomologicalComplex.mapHomologicalComplexExtendIso (prodSndSummand.{u, v, w} J (B := B) (D := D))
      ((AlgebraicTopology.alternatingFaceMapComplex _).obj
        (baseChangedCotangentSimplicialModule.{u, v, w} J g (prodGraph J h)))
      (ComplexShape.embeddingUpIntLE 0)).symm ≪≫
    ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor _).mapIso
      ((AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
          (prodSndSummand.{u, v, w} J (B := B) (D := D))).app
          (baseChangedCotangentSimplicialModule.{u, v, w} J g (prodGraph J h)) ≪≫
        (AlgebraicTopology.alternatingFaceMapComplex _).mapIso
          (Functor.isoWhiskerLeft (cotangentSimplicialModule.{u, v, w} J g).object
            (prodGraphSummandIso J h)))

/-- The comparison of first vertices, in degree `-n`. -/
lemma prodGraphBaseChangedIso_hom_f (n : ℕ) :
    (prodGraphBaseChangedIso J g h).hom.f (-(n : ℤ)) =
      (prodSndSummand.{u, v, w} J (B := B) (D := D)).map
          (baseChangedCotangentComplex_degreeIso.{u, v, w} J g (prodGraph J h) n).hom ≫
        (prodGraphSummandIso J h).hom.app
          ((cotangentSimplicialModule.{u, v, w} J g).object.obj (op ⦋n⦌)) ≫
        (baseChangedCotangentComplex_degreeIso.{u, v, w} J g h n).inv := by
  have hn : (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n = -(n : ℤ) := by simp
  let E := prodSndSummand.{u, v, w} J (B := B) (D := D)
  let K := (AlgebraicTopology.alternatingFaceMapComplex _).obj
    (baseChangedCotangentSimplicialModule.{u, v, w} J g (prodGraph J h))
  have h₁ := HomologicalComplex.mapHomologicalComplexExtendIso_hom_f E K
    (ComplexShape.embeddingUpIntLE 0) hn
  have h₁' : (HomologicalComplex.mapHomologicalComplexExtendIso E K
      (ComplexShape.embeddingUpIntLE 0)).inv.f (-(n : ℤ)) =
      E.map (K.extendXIso (ComplexShape.embeddingUpIntLE 0) hn).hom ≫
        (((E.mapHomologicalComplex _).obj K).extendXIso
          (ComplexShape.embeddingUpIntLE 0) hn).inv := by
    rw [← cancel_mono ((HomologicalComplex.mapHomologicalComplexExtendIso E K
      (ComplexShape.embeddingUpIntLE 0)).hom.f (-(n : ℤ))), ← HomologicalComplex.comp_f,
      Iso.inv_hom_id, HomologicalComplex.id_f, h₁, Category.assoc, Iso.inv_hom_id_assoc,
      ← E.map_comp, Iso.hom_inv_id, E.map_id]
    rfl
  let I := (AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso E).app
      (baseChangedCotangentSimplicialModule.{u, v, w} J g (prodGraph J h)) ≪≫
    (AlgebraicTopology.alternatingFaceMapComplex _).mapIso
      (Functor.isoWhiskerLeft (cotangentSimplicialModule.{u, v, w} J g).object
        (prodGraphSummandIso J h))
  change ((HomologicalComplex.mapHomologicalComplexExtendIso E K
      (ComplexShape.embeddingUpIntLE 0)).inv ≫
    HomologicalComplex.extendMap I.hom (ComplexShape.embeddingUpIntLE 0)).f (-(n : ℤ)) = _
  rw [HomologicalComplex.comp_f, h₁', HomologicalComplex.extendMap_f _ _ hn]
  have hI : I.hom.f n = (prodGraphSummandIso J h).hom.app
      ((cotangentSimplicialModule.{u, v, w} J g).object.obj (op ⦋n⦌)) := by
    simp [I]
  let A := ((E.mapHomologicalComplex _).obj K).extendXIso (ComplexShape.embeddingUpIntLE 0) hn
  let Z := ((AlgebraicTopology.alternatingFaceMapComplex _).obj
    (baseChangedCotangentSimplicialModule.{u, v, w} J g h)).extendXIso
      (ComplexShape.embeddingUpIntLE 0) hn
  calc _ = E.map (K.extendXIso (ComplexShape.embeddingUpIntLE 0) hn).hom ≫ (A.inv ≫ A.hom) ≫
        I.hom.f n ≫ Z.inv := by
          simp only [Category.assoc]
          rfl
    _ = E.map (K.extendXIso (ComplexShape.embeddingUpIntLE 0) hn).hom ≫
        (prodGraphSummandIso J h).hom.app
          ((cotangentSimplicialModule.{u, v, w} J g).object.obj (op ⦋n⦌)) ≫ Z.inv := by
          rw [Iso.inv_hom_id, Category.id_comp, hI]
    _ = _ := rfl

/-- The degreewise base change `L_{B/A} ⊗_B D'` vanishes in positive cohomological degrees. -/
lemma baseChangedCotangentComplex_isZero_pos {D' : Sheaf J CommRingCat.{max u v w}}
    (h' : B ⟶ D') (m : ℤ) (hm : 0 < m) :
    IsZero ((baseChangedCotangentComplex.{u, v, w} J g h').X m) := by
  apply HomologicalComplex.isZero_extend_X
  intro n
  simp only [ComplexShape.embeddingUpIntLE_f]
  omega

/-- **The first arrows of the two towers correspond**: the second summand of the base change
along `b ↦ (b, h b)` is the base change along `h`, through the identification of the first
vertices and the second comparison of Tag 08SY. -/
theorem prodSndCotangentComparison_baseChange :
    (prodSndSummandComplex.{u, v, w} J (B := B) (D := D)).map
        (towerCotangentBaseChange.{u, v, w} J g (prodGraph J h)) ≫
      prodSndCotangentComparison.{u, v, w} J (g ≫ prodGraph J h) (g ≫ h)
        (prodGraph_square_base J g h) =
    (prodGraphBaseChangedIso J g h).hom ≫ towerCotangentBaseChange.{u, v, w} J g h := by
  refine hom_ext_of_nonpos _ _ _ _ (fun i hi => ((prodSndSummand.{u, v, w} J (B := B)
    (D := D)).map_isZero (baseChangedCotangentComplex_isZero_pos J g _ i hi))) fun n => ?_
  have l₁ := towerCotangentBaseChange_f J g (prodGraph J h) n
  have l₂ := towerCotangentBaseChange_f J g h n
  have l₃ := prodSndCotangentComparison_f J (g ≫ prodGraph J h) (g ≫ h)
    (prodGraph_square_base J g h) n
  have l₄ := prodGraphBaseChangedIso_hom_f J g h n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    l₁, l₂, l₃, l₄, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id_map_assoc, Iso.inv_hom_id_assoc]
  rw [prodSndSummand_baseChange_term_assoc]

end FirstArrow

/-! ## The triangle -/

/-- **Stacks 08SZ, the fundamental triangle.** Let `A ⟶ B ⟶ D` be homomorphisms of sheaves of
commutative rings on a site. The triangle

`L_{B/A} ⊗_B D ⟶ L_{D/A} ⟶ L_{D/B} ⟶ (L_{B/A} ⊗_B D)[1]`

with first two arrows `CategoryTheory.Sheaf.towerCotangentBaseChange` and
`CategoryTheory.Sheaf.towerCotangentChangeOfBase` is distinguished in `D(D)`; its first vertex
is `L_{B/A} ⊗^L_B D` by `CategoryTheory.Sheaf.baseChangedCotangentComplexDerivedIso`.

This is the argument of the source: the homomorphism `B ⟶ B × D`, `b ↦ (b, h b)`, is injective
on sections, so the triangle of `A ⟶ B ⟶ B × D` is distinguished
(`CategoryTheory.Sheaf.exists_distTriang_towerCotangent_of_injective`), and the exact second
summand functor `Mod(B × D) ⥤ Mod(D)` carries it to the triangle of `A ⟶ B ⟶ D`. -/
@[stacks 08SZ "the distinguished triangle `L_{B/A} ⊗^L_B D → L_{D/A} → L_{D/B} → (L_{B/A}
⊗^L_B D)[1]` with the canonical first two arrows, in `D(D)`, on any site; the first vertex is
identified with `L_{B/A} ⊗^L_B D` by `CategoryTheory.Sheaf.baseChangedCotangentComplexDerivedIso`"]
theorem exists_distTriang_towerCotangent
    [HasDerivedCategory.{t} (targetModules.{u, v, w} J D)] :
    ∃ δ : cotangentComplexDerived.{u, v, w, t} J h ⟶
        (DerivedCategory.Q.obj (baseChangedCotangentComplex.{u, v, w} J g h))⟦(1 : ℤ)⟧,
      Triangle.mk (DerivedCategory.Q.map (towerCotangentBaseChange.{u, v, w} J g h))
          (DerivedCategory.Q.map (towerCotangentChangeOfBase.{u, v, w} J g h)) δ ∈
        distTriang (DerivedCategory (targetModules.{u, v, w} J D)) := by
  let := HasDerivedCategory.standard (targetModules.{u, v, w} J (prodObj J B D))
  obtain ⟨δ', hT'⟩ := exists_distTriang_towerCotangent_of_injective J g (prodGraph J h)
    (injective_prodGraph J h)
  let E := prodSndSummand.{u, v, w} J (B := B) (D := D)
  let Φ := E.mapDerivedCategory
  have hΦ := Φ.map_distinguished _ hT'
  have q₂ := quasiIso_prodSndCotangentComparison J (g ≫ prodGraph J h) g (g ≫ h)
    (prod.hom_ext (by rw [Category.assoc, prodRingHom_fst, prodRingHom_fst, Category.comp_id])
      (by rw [Category.assoc, prodRingHom_snd, prodRingHom_snd])) (prodGraph_square_base J g h)
  have q₃ := quasiIso_prodSndCotangentComparison J (prodGraph J h) (𝟙 B) h rfl
    (prodGraph_square_top J h)
  let i₁ := E.mapDerivedCategoryFactors.app (baseChangedCotangentComplex.{u, v, w} J g
      (prodGraph J h)) ≪≫ DerivedCategory.Q.mapIso (prodGraphBaseChangedIso J g h)
  let i₂ := E.mapDerivedCategoryFactors.app (cotangentComplex.{u, v, w} J (g ≫ prodGraph J h)) ≪≫
    asIso (DerivedCategory.Q.map (prodSndCotangentComparison.{u, v, w} J (g ≫ prodGraph J h)
      (g ≫ h) (prodGraph_square_base J g h)))
  let i₃ := E.mapDerivedCategoryFactors.app (cotangentComplex.{u, v, w} J (prodGraph J h)) ≪≫
    asIso (DerivedCategory.Q.map (prodSndCotangentComparison.{u, v, w} J (prodGraph J h) h
      (prodGraph_square_top J h)))
  have c₁ : Φ.map (DerivedCategory.Q.map (towerCotangentBaseChange.{u, v, w} J g
        (prodGraph J h))) ≫ i₂.hom =
      i₁.hom ≫ DerivedCategory.Q.map (towerCotangentBaseChange.{u, v, w} J g h) := by
    dsimp only [i₁, i₂, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, asIso_hom]
    rw [Functor.mapDerivedCategoryFactors_hom_naturality_assoc, ← Functor.map_comp,
      prodSndCotangentComparison_baseChange, Functor.map_comp, Category.assoc]
  have c₂ : Φ.map (DerivedCategory.Q.map (towerCotangentChangeOfBase.{u, v, w} J g
        (prodGraph J h))) ≫ i₃.hom =
      i₂.hom ≫ DerivedCategory.Q.map (towerCotangentChangeOfBase.{u, v, w} J g h) := by
    dsimp only [i₂, i₃, Iso.trans_hom, Iso.app_hom, asIso_hom]
    rw [Functor.mapDerivedCategoryFactors_hom_naturality_assoc, ← Functor.map_comp,
      prodSndCotangentComparison_changeOfBase, Functor.map_comp, Category.assoc]
  let T' := Triangle.mk (DerivedCategory.Q.map (towerCotangentBaseChange.{u, v, w} J g
    (prodGraph J h))) (DerivedCategory.Q.map (towerCotangentChangeOfBase.{u, v, w} J g
      (prodGraph J h))) δ'
  let δ₀ : Φ.obj (DerivedCategory.Q.obj (cotangentComplex.{u, v, w} J (prodGraph J h))) ⟶
      (Φ.obj (DerivedCategory.Q.obj (baseChangedCotangentComplex.{u, v, w} J g
        (prodGraph J h))))⟦(1 : ℤ)⟧ := (Φ.mapTriangle.obj T').mor₃
  refine ⟨i₃.inv ≫ δ₀ ≫ i₁.hom⟦(1 : ℤ)⟧',
    isomorphic_distinguished _ hΦ _ (Triangle.isoMk _ _ i₁.symm i₂.symm i₃.symm ?_ ?_ ?_)⟩
  · exact (CommSq.vert_inv (g := i₁) (h := i₂) ⟨c₁⟩).w
  · exact (CommSq.vert_inv (g := i₂) (h := i₃) ⟨c₂⟩).w
  · change (i₃.inv ≫ δ₀ ≫ i₁.hom⟦(1 : ℤ)⟧') ≫ i₁.inv⟦(1 : ℤ)⟧' = i₃.inv ≫ δ₀
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, Functor.map_id,
      Category.comp_id]

end CategoryTheory.Sheaf

end
