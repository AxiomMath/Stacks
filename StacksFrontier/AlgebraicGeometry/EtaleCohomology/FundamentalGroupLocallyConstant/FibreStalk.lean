module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.Sets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Stalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointStalkMap
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical

/-!
# The stalk of the sheaf of a finite étale cover is its geometric fibre

Let `X` be a scheme and `s̄` a geometric point of `X`.  By Tag 03RV a finite étale cover
`Y → X` is the same thing as the finite locally constant sheaf of sets `h_Y` it represents on
`X_étale`.  The stalk of `h_Y` at `s̄` is the geometric fibre `Y_s̄ = Mor_X(s̄, Y)` of `Y`,
naturally in `Y`: a germ at a pointed étale neighbourhood `(U, ū)` of a section `t : U → Y`
goes to the lift `ū ≫ t` of `s̄`.  An endomorphism `a` of `s̄` acts on the stalk by the map of
Tag 04FN and on the fibre by precomposition with `a`, and the identification intertwines them.

## Main definitions

* `AlgebraicGeometry.uliftCompEtaleStalkPresheafFunctorIso`: stalks commute with raising the
  universe of a presheaf of sets.
* `AlgebraicGeometry.finiteEtaleStalkIso`: the stalk at `s̄` of the finite locally constant sheaf
  of sets of a finite étale cover is its geometric fibre at `s̄`, naturally in the cover.

## Main results

* `AlgebraicGeometry.finiteEtaleStalkIso_geometricPointStalkMap`: the action of an endomorphism
  of `s̄` on the stalk is precomposition on the fibre.

## References

* [Stacks Project, Tag 03RV](https://stacks.math.columbia.edu/tag/03RV)
* [Stacks Project, Tag 04FN](https://stacks.math.columbia.edu/tag/04FN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry

section ULift

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- **Stalks commute with raising the universe of a presheaf of sets**: the forgetful functor
`uliftFunctor` preserves colimits. -/
public def uliftCompEtaleStalkPresheafFunctorIso :
    (Functor.whiskeringRight _ _ _).obj uliftFunctor.{w} ⋙
        etaleStalkPresheafFunctor B S hS s (Type max u w) ≅
      etaleStalkPresheafFunctor B S hS s (Type u) ⋙ uliftFunctor.{w} :=
  Functor.isoWhiskerLeft ((Functor.whiskeringLeft _ _ _).obj
    (CategoryOfElements.π (geometricPointFiber B S hS s)).op)
    (preservesColimitNatIso uliftFunctor.{w}).symm

/-- The comparison on germs: the germ of `⟨σ⟩` goes to `⟨germ of σ⟩`. -/
@[reassoc]
public theorem ι_uliftCompEtaleStalkPresheafFunctorIso_hom
    (P : (SmallEtale B S hS)ᵒᵖ ⥤ Type u) (U : (geometricPointFiber B S hS s).Elementsᵒᵖ) :
    colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙
          P ⋙ uliftFunctor.{w}) U ≫
        (uliftCompEtaleStalkPresheafFunctorIso.{w} B S hS s).hom.app P =
      uliftFunctor.{w}.map
        (colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙ P) U) :=
  ι_preservesColimitIso_inv uliftFunctor.{w}
    ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙ P) U

end ULift


section Representable

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {s t : GeometricPoint S}

/-- The map of Tag 04FN commutes with raising the universe of a presheaf of sets. -/
public theorem geometricPointStalkMap_uliftCompEtaleStalkPresheafFunctorIso
    (a : GeometricPoint.Hom s t) (P : (SmallEtale B S hS)ᵒᵖ ⥤ Type u) :
    (geometricPointStalkMap B S hS a (Type max u w)).app (P ⋙ uliftFunctor.{w}) ≫
        (uliftCompEtaleStalkPresheafFunctorIso.{w} B S hS s).hom.app P =
      (uliftCompEtaleStalkPresheafFunctorIso.{w} B S hS t).hom.app P ≫
        uliftFunctor.{w}.map ((geometricPointStalkMap B S hS a (Type u)).app P) := by
  refine colimit.hom_ext fun U => ?_
  dsimp only [geometricPointStalkMap]
  refine (colimit.ι_pre_assoc ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙
    P ⋙ uliftFunctor.{w}) (neighborhoodFunctor B S hS a).op U _).trans ?_
  refine (ι_uliftCompEtaleStalkPresheafFunctorIso_hom.{w} B S hS s P _).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_ (congrArg (· ≫ _)
    (ι_uliftCompEtaleStalkPresheafFunctorIso_hom.{w} B S hS t P U)).symm
  refine Eq.trans ?_ (uliftFunctor.{w}.map_comp _ _)
  exact congrArg uliftFunctor.{w}.map (colimit.ι_pre _ _ _).symm

/-- The identification of the stalk of a representable presheaf with the geometric fibre
intertwines the map of Tag 04FN with precomposition by the morphism of geometric points. -/
public theorem geometricPointStalkMap_yonedaCompEtaleStalkPresheafFunctorIso
    (a : GeometricPoint.Hom s t) (X : SmallEtale B S hS) :
    (geometricPointStalkMap B S hS a (Type u)).app (yoneda.obj X) ≫
        (yonedaCompEtaleStalkPresheafFunctorIso B S hS s).hom.app X =
      (yonedaCompEtaleStalkPresheafFunctorIso B S hS t).hom.app X ≫
        (geometricPointFiberMap B S hS a).app X := by
  refine colimit.hom_ext fun U => ?_
  dsimp only [geometricPointStalkMap]
  refine (colimit.ι_pre_assoc ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙
    yoneda.obj X) (neighborhoodFunctor B S hS a).op U _).trans ?_
  refine (colimit_ι_comp_yonedaCompEtaleStalkPresheafFunctorIso_hom B S hS s X _).trans ?_
  refine Eq.trans ?_ (congrArg (· ≫ (geometricPointFiberMap B S hS a).app X)
    (colimit_ι_comp_yonedaCompEtaleStalkPresheafFunctorIso_hom B S hS t X U.unop)).symm
  rfl

/-- **The stalk of a representable sheaf of sets, in the universe of the small étale topos.**
The stalk at `s̄` of the sheaf `h_X` represented by an object `X` of the small étale site is the
set of lifts of `s̄` to `X`, naturally in `X`: on a subcanonical site the sheafified Yoneda
embedding is the Yoneda embedding, raising universes commutes with stalks, and the stalk of a
representable presheaf is the fibre of the geometric point. -/
public def sheafifiedYonedaStalkIso (s : GeometricPoint S) :
    Sheaf.sheafifiedYoneda (SmallEtale.topology B S hS) ⋙
        sheafToPresheaf (SmallEtale.topology B S hS) (Type (u + 1)) ⋙
          etaleStalkPresheafFunctor B S hS s (Type (u + 1)) ≅
      geometricPointFiber B S hS s ⋙ uliftFunctor.{u + 1} :=
  Functor.isoWhiskerRight (Sheaf.uliftYonedaIsoSheafifiedYoneda
      (SmallEtale.topology B S hS)).symm _ ≪≫
    Functor.isoWhiskerLeft yoneda (uliftCompEtaleStalkPresheafFunctorIso.{u + 1} B S hS s) ≪≫
    Functor.isoWhiskerRight (yonedaCompEtaleStalkPresheafFunctorIso B S hS s) uliftFunctor.{u + 1}

/-- The identification of the stalk of a representable sheaf with the geometric fibre
intertwines the map of Tag 04FN along `a : s̄ ⟶ t̄` with precomposition by `a`. -/
public theorem geometricPointStalkMap_sheafifiedYonedaStalkIso (a : GeometricPoint.Hom s t)
    (X : SmallEtale B S hS) :
    (geometricPointStalkMap B S hS a (Type (u + 1))).app
          ((Sheaf.sheafifiedYoneda (SmallEtale.topology B S hS)).obj X).obj ≫
        (sheafifiedYonedaStalkIso B S hS s).hom.app X =
      (sheafifiedYonedaStalkIso B S hS t).hom.app X ≫
        uliftFunctor.{u + 1}.map ((geometricPointFiberMap B S hS a).app X) := by
  let A : ∀ r : GeometricPoint S, _ := fun r => (etaleStalkPresheafFunctor B S hS r
    (Type (u + 1))).map ((sheafToPresheaf (SmallEtale.topology B S hS) (Type (u + 1))).map
      ((Sheaf.uliftYonedaIsoSheafifiedYoneda (SmallEtale.topology B S hS)).inv.app X))
  have h2 := geometricPointStalkMap_uliftCompEtaleStalkPresheafFunctorIso.{u + 1} B S hS a
    (yoneda.obj X)
  have h3 := congrArg uliftFunctor.{u + 1}.map
    (geometricPointStalkMap_yonedaCompEtaleStalkPresheafFunctorIso B S hS a X)
  simp only [Functor.map_comp] at h3
  show _ ≫ (A s ≫ (uliftCompEtaleStalkPresheafFunctorIso.{u + 1} B S hS s).hom.app
      (yoneda.obj X) ≫ uliftFunctor.{u + 1}.map
        ((yonedaCompEtaleStalkPresheafFunctorIso B S hS s).hom.app X)) =
    (A t ≫ (uliftCompEtaleStalkPresheafFunctorIso.{u + 1} B S hS t).hom.app
      (yoneda.obj X) ≫ uliftFunctor.{u + 1}.map
        ((yonedaCompEtaleStalkPresheafFunctorIso B S hS t).hom.app X)) ≫ _
  have h1' : (geometricPointStalkMap B S hS a (Type (u + 1))).app
        ((Sheaf.sheafifiedYoneda (SmallEtale.topology B S hS)).obj X).obj ≫ A s =
      A t ≫ (geometricPointStalkMap B S hS a (Type (u + 1))).app
        (yoneda.obj X ⋙ uliftFunctor.{u + 1}) :=
    ((geometricPointStalkMap B S hS a (Type (u + 1))).naturality
      ((sheafToPresheaf (SmallEtale.topology B S hS) (Type (u + 1))).map
        ((Sheaf.uliftYonedaIsoSheafifiedYoneda (SmallEtale.topology B S hS)).inv.app X))).symm
  simp only [Category.assoc]
  rw [reassoc_of% h1']
  refine (Category.assoc _ _ _).trans (congrArg (A t ≫ ·) ?_)
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h2)).trans ?_
  refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
  exact congrArg (_ ≫ ·) h3

end Representable

section Preserves

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {s t : GeometricPoint S}
  {A : Type*} [Category* A] {A' : Type*} [Category* A']
  [HasColimitsOfShape (geometricPointFiber B S hS s).Elementsᵒᵖ A]
  [HasColimitsOfShape (geometricPointFiber B S hS t).Elementsᵒᵖ A]
  [HasColimitsOfShape (geometricPointFiber B S hS s).Elementsᵒᵖ A']
  [HasColimitsOfShape (geometricPointFiber B S hS t).Elementsᵒᵖ A']
  (R : A ⥤ A') [PreservesColimitsOfShape (geometricPointFiber B S hS s).Elementsᵒᵖ R]
  [PreservesColimitsOfShape (geometricPointFiber B S hS t).Elementsᵒᵖ R]

/-- `colimit.pre` commutes with the comparison isomorphisms of a colimit-preserving functor. -/
public theorem map_pre_preservesColimitIso_hom {J K : Type*} [Category* J] [Category* K]
    (F : J ⥤ A) (E : K ⥤ J) [HasColimitsOfShape J A] [HasColimitsOfShape K A]
    [HasColimitsOfShape J A'] [HasColimitsOfShape K A'] [PreservesColimitsOfShape J R]
    [PreservesColimitsOfShape K R] :
    R.map (colimit.pre F E) ≫ (preservesColimitIso R F).hom =
      (preservesColimitIso R (E ⋙ F)).hom ≫ colimit.pre (F ⋙ R) E := by
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv]
  refine colimit.hom_ext fun j => ?_
  rw [ι_preservesColimitIso_inv_assoc, ← R.map_comp, colimit.ι_pre]
  exact ((colimit.ι_pre_assoc (F ⋙ R) E j _).trans (ι_preservesColimitIso_inv R _ _)).symm

/-- The map of Tag 04FN commutes with a functor preserving the colimits defining the stalks. -/
public theorem geometricPointStalkMap_preservesColimitIso (a : GeometricPoint.Hom s t)
    (P : (SmallEtale B S hS)ᵒᵖ ⥤ A) :
    R.map ((geometricPointStalkMap B S hS a A).app P) ≫
        (preservesColimitIso R ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙
          P)).hom =
      (preservesColimitIso R ((CategoryOfElements.π (geometricPointFiber B S hS t)).op ⋙
          P)).hom ≫ (geometricPointStalkMap B S hS a A').app (P ⋙ R) :=
  map_pre_preservesColimitIso_hom R _ (neighborhoodFunctor B S hS a).op

end Preserves

section FiniteEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- Precomposition with a morphism of geometric points `a : s̄ ⟶ t̄`, from the geometric fibres
at `t̄` of the finite étale covers of `X` to those at `s̄`. -/
public def finiteEtaleFiberMap {S : Scheme.{u}} {s t : GeometricPoint S}
    (a : GeometricPoint.Hom s t) : finiteEtaleFiberFunctor t ⟶ finiteEtaleFiberFunctor s where
  app Y := ↾ (fun p => ⟨a.hom ≫ p.1, by rw [Category.assoc, p.2]; exact a.comm⟩)
  naturality Y Z f := by
    ext p
    exact Subtype.ext (Category.assoc _ _ _).symm

/-- The point of `Y_s̄` that `finiteEtaleFiberMap a` assigns to a point `p` of `Y_t̄` is the
composite `a.hom ≫ p`. -/
@[simp]
public theorem finiteEtaleFiberMap_app_coe {S : Scheme.{u}} {s t : GeometricPoint S}
    (a : GeometricPoint.Hom s t) (Y : FiniteEtaleOver S) (p : finiteEtaleFiber t Y) :
    ((finiteEtaleFiberMap a).app Y p).1 = a.hom ≫ p.1 :=
  rfl

/-- On a finite object of the small étale site, the fibre of the geometric point is the
geometric fibre of the corresponding finite étale cover. -/
public def geometricPointFiberFiniteEtaleIso (s : GeometricPoint X.1) :
    (finiteSmallEtaleObjects B X).ι ⋙ geometricPointFiber B X.1 X.2 s ≅
      finiteEtaleFromSmallEtale B X ⋙ finiteEtaleFiberFunctor s :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- **The stalk at a geometric point `s̄` of the finite locally constant sheaf of sets of a
finite étale cover `Y` is the geometric fibre `Y_s̄`**, naturally in `Y` (Tag 03RV and the
computation of the stalk of a representable sheaf). -/
public def finiteEtaleStalkIso (s : GeometricPoint X.1) :
    finiteEtaleToFiniteLocallyConstant B X ⋙ ObjectProperty.ι _ ⋙
        sheafToPresheaf (SmallEtale.topology B X.1 X.2) (Type (u + 1)) ⋙
          etaleStalkPresheafFunctor B X.1 X.2 s (Type (u + 1)) ≅
      finiteEtaleFiberFunctor s ⋙ uliftFunctor.{u + 1} :=
  Functor.isoWhiskerLeft ((finiteEtaleSiteEquivalence B X).inverse ⋙
      (finiteSmallEtaleObjects B X).ι) (sheafifiedYonedaStalkIso B X.1 X.2 s) ≪≫
    Functor.isoWhiskerLeft (finiteEtaleSiteEquivalence B X).inverse
      (Functor.isoWhiskerRight (geometricPointFiberFiniteEtaleIso B X s) uliftFunctor.{u + 1}) ≪≫
    Functor.isoWhiskerRight (finiteEtaleSiteEquivalence B X).counitIso
      (finiteEtaleFiberFunctor s ⋙ uliftFunctor.{u + 1})

/-- The identification of the stalk of the sheaf of a finite étale cover with its geometric
fibre intertwines the map of Tag 04FN along `a : s̄ ⟶ t̄` with precomposition by `a`. -/
public theorem geometricPointStalkMap_finiteEtaleStalkIso {s t : GeometricPoint X.1}
    (a : GeometricPoint.Hom s t) (Y : FiniteEtaleOver X.1) :
    (geometricPointStalkMap B X.1 X.2 a (Type (u + 1))).app
          ((finiteEtaleToFiniteLocallyConstant B X).obj Y).obj.obj ≫
        (finiteEtaleStalkIso B X s).hom.app Y =
      (finiteEtaleStalkIso B X t).hom.app Y ≫
        uliftFunctor.{u + 1}.map ((finiteEtaleFiberMap a).app Y) := by
  have h := geometricPointStalkMap_sheafifiedYonedaStalkIso B X.1 X.2 a
    ((finiteEtaleSiteEquivalence B X).inverse.obj Y).1
  show _ ≫ ((sheafifiedYonedaStalkIso B X.1 X.2 s).hom.app _ ≫ 𝟙 _ ≫
      uliftFunctor.{u + 1}.map ((finiteEtaleFiberFunctor s).map
        ((finiteEtaleSiteEquivalence B X).counitIso.hom.app Y))) =
    ((sheafifiedYonedaStalkIso B X.1 X.2 t).hom.app _ ≫ 𝟙 _ ≫
      uliftFunctor.{u + 1}.map ((finiteEtaleFiberFunctor t).map
        ((finiteEtaleSiteEquivalence B X).counitIso.hom.app Y))) ≫ _
  simp only [Category.id_comp]
  refine ((reassoc_of% h) _).trans (Eq.trans (congrArg (_ ≫ ·) ?_) (Category.assoc _ _ _).symm)
  refine (uliftFunctor.{u + 1}.map_comp _ _).symm.trans
    (Eq.trans ?_ (uliftFunctor.{u + 1}.map_comp _ _))
  exact congrArg uliftFunctor.{u + 1}.map
    ((finiteEtaleFiberMap a).naturality ((finiteEtaleSiteEquivalence B X).counitIso.hom.app Y))

/-- **The stalk at `s̄` of a finite locally constant sheaf of sets `G` is the geometric fibre at
`s̄` of the finite étale cover representing `G`** (Tag 03RV), naturally in `G`. -/
public def finiteLocallyConstantStalkIso (s : GeometricPoint X.1) :
    ObjectProperty.ι _ ⋙ sheafToPresheaf (SmallEtale.topology B X.1 X.2) (Type (u + 1)) ⋙
        etaleStalkPresheafFunctor B X.1 X.2 s (Type (u + 1)) ≅
      (finiteLocallyConstantFiniteEtaleEquivalence B X).functor ⋙ finiteEtaleFiberFunctor s ⋙
        uliftFunctor.{u + 1} :=
  Functor.isoWhiskerRight (finiteLocallyConstantFiniteEtaleEquivalence B X).unitIso
      (ObjectProperty.ι _ ⋙ sheafToPresheaf (SmallEtale.topology B X.1 X.2) (Type (u + 1)) ⋙
        etaleStalkPresheafFunctor B X.1 X.2 s (Type (u + 1))) ≪≫
    Functor.isoWhiskerLeft (finiteLocallyConstantFiniteEtaleEquivalence B X).functor
      (finiteEtaleStalkIso B X s)

/-- The identification of the stalk of a finite locally constant sheaf of sets with the
geometric fibre of its finite étale cover intertwines the map of Tag 04FN along `a : s̄ ⟶ t̄`
with precomposition by `a`. -/
public theorem geometricPointStalkMap_finiteLocallyConstantStalkIso {s t : GeometricPoint X.1}
    (a : GeometricPoint.Hom s t) (G : FiniteLocallyConstantSheaf B X) :
    (geometricPointStalkMap B X.1 X.2 a (Type (u + 1))).app G.obj.obj ≫
        (finiteLocallyConstantStalkIso B X s).hom.app G =
      (finiteLocallyConstantStalkIso B X t).hom.app G ≫
        uliftFunctor.{u + 1}.map ((finiteEtaleFiberMap a).app
          ((finiteLocallyConstantFiniteEtaleEquivalence B X).functor.obj G)) := by
  have h := geometricPointStalkMap_finiteEtaleStalkIso B X a
    ((finiteLocallyConstantFiniteEtaleEquivalence B X).functor.obj G)
  have hn := (geometricPointStalkMap B X.1 X.2 a (Type (u + 1))).naturality
    ((finiteLocallyConstantFiniteEtaleEquivalence B X).unitIso.hom.app G).hom.hom
  show _ ≫ (etaleStalkPresheafFunctor B X.1 X.2 s (Type (u + 1))).map
      ((finiteLocallyConstantFiniteEtaleEquivalence B X).unitIso.hom.app G).hom.hom ≫ _ =
    ((etaleStalkPresheafFunctor B X.1 X.2 t (Type (u + 1))).map
      ((finiteLocallyConstantFiniteEtaleEquivalence B X).unitIso.hom.app G).hom.hom ≫ _) ≫ _
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hn.symm)).trans ?_
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h).trans (Category.assoc _ _ _).symm)

end FiniteEtale

end AlgebraicGeometry

end
