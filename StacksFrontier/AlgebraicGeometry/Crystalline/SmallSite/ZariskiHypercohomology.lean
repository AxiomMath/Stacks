module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ZariskiDirectImage
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksFrontier.CategoryTheory.Sites.Simplicial.VanishingCohomology
public import StacksFrontier.Homology.Ext.CorepresentedNaturality
public import StacksFrontier.Homology.Ext.DerivedCoyoneda

/-!
# Zariski hypercohomology is corepresented by the constant sheaf on the integers

Let `X` be the scheme of a global crystalline situation and `K` an object of the bounded below
derived category of abelian sheaves on the small Zariski site `X_Zar`. The cohomology of the
derived global sections of `K` is identified, naturally in `K`, with morphisms out of a shift of
the constant sheaf on `ℤ`:

`H^i(RΓ(X_Zar, K)) ≃+ Hom_{D(Ab(X_Zar))}(ℤ_X[0]⟦-i⟧, K)`.

More generally, for an additive functor `T` corepresented by an object `Z` of an abelian category
with enough injectives, `H^n(RT(K)) ≃+ Hom_{D}(Z[0], K⟦n⟧)`. The two sides lie in different
universes, so the comparison is an additive equivalence of groups.

## Main definitions

* `Stacks.Cohomology.Corepresented.homologyMapHomologicalComplexAddEquiv`: for an additive
  functor `T` corepresented by an object `Z` and a K-injective complex `L`, the cohomology of
  `T` applied to `L` termwise is `Hom_{D}(Z[0], L⟦n⟧)`.
* `Stacks.Cohomology.Corepresented.rightDerivedHomologyAddEquiv`:
  `H^n(RT(K)) ≃+ Hom_{D}(Z[0], K⟦n⟧)` for `K` in `D⁺`.
* `Stacks.Cohomology.Corepresented.rightDerivedHomologyShiftAddEquiv`: the same, as morphisms
  out of `Z[0]⟦-n⟧`.

In the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`:

* `zariskiIntegerSheaf`: the constant sheaf `ℤ_X` on `X_Zar`.
* `zariskiGlobalSectionsCorepresentation`: `Γ(X_Zar, -)` is corepresented by `ℤ_X`.
* `derivedZariskiGlobalSectionsHomologyAddEquiv`:
  `H^i(RΓ(X_Zar, K)) ≃+ Hom_{D(Ab(X_Zar))}(ℤ_X[0], K⟦i⟧)`.
* `derivedZariskiGlobalSectionsHomologyShiftAddEquiv`:
  `H^i(RΓ(X_Zar, K)) ≃+ Hom_{D(Ab(X_Zar))}(ℤ_X[0]⟦-i⟧, K)`.

## Main results

* `Stacks.Cohomology.Corepresented.rightDerivedHomologyAddEquiv_naturality` and
  `Stacks.Cohomology.Corepresented.rightDerivedHomologyShiftAddEquiv_naturality`: the two
  comparisons are natural in `K`.
* In `Crystalline.GlobalCrystallineSituation.SmallSite`,
  `derivedZariskiGlobalSectionsHomologyAddEquiv_naturality` and
  `derivedZariskiGlobalSectionsHomologyShiftAddEquiv_naturality`: the same for `RΓ(X_Zar, -)`.

## References

* [Stacks Project, Tag 07QA](https://stacks.math.columbia.edu/tag/07QA)
* [Stacks Project, Tag 0A64](https://stacks.math.columbia.edu/tag/0A64)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' v u

namespace Stacks.Cohomology.Corepresented

/-! ### Transporting a morphism group along isomorphisms -/

/-- A pair of isomorphisms induces an additive equivalence of morphism groups. -/
def homCongrAddEquiv {C : Type*} [Category* C] [Preadditive C] {X X' Y Y' : C}
    (φ : X ≅ X') (ψ : Y ≅ Y') : (X ⟶ Y) ≃+ (X' ⟶ Y') where
  toFun f := φ.inv ≫ f ≫ ψ.hom
  invFun g := φ.hom ≫ g ≫ ψ.inv
  left_inv f := by simp
  right_inv g := by simp
  map_add' f g := by simp [Preadditive.add_comp, Preadditive.comp_add]

/-- Morphisms out of a negative shift are morphisms into the positive shift. -/
def shiftHomAddEquiv {C : Type*} [Category* C] [Preadditive C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] (X Y : C) (n : ℤ) :
    (X⟦-n⟧ ⟶ Y) ≃+ (X ⟶ Y⟦n⟧) :=
  (AddEquiv.ofBijective (shiftFunctor C n).mapAddHom
      ⟨(shiftFunctor C n).map_injective, (shiftFunctor C n).map_surjective⟩).trans
    (homCongrAddEquiv ((shiftFunctorCompIsoId C (-n) n (by omega)).app X) (Iso.refl (Y⟦n⟧)))

/-- `shiftHomAddEquiv` is natural in its target: it carries postcomposition with `ψ` to
postcomposition with `ψ⟦n⟧`. -/
theorem shiftHomAddEquiv_comp {C : Type*} [Category* C] [Preadditive C] [HasShift C ℤ]
    [∀ m : ℤ, (shiftFunctor C m).Additive] (X Y Y' : C) (n : ℤ) (ψ : Y ⟶ Y')
    (g : X⟦-n⟧ ⟶ Y) :
    shiftHomAddEquiv X Y' n (g ≫ ψ) =
      shiftHomAddEquiv X Y n g ≫ (shiftFunctor C n).map ψ := by
  simp only [shiftHomAddEquiv, homCongrAddEquiv, AddEquiv.trans_apply, AddEquiv.coe_mk,
    Equiv.coe_fn_mk, Iso.refl_hom, Category.comp_id, Category.assoc]
  congr 1
  exact (shiftFunctor C n).map_comp g ψ

/-- The inverse of `shiftHomAddEquiv` is natural in its target: it carries postcomposition with
`ψ⟦n⟧` to postcomposition with `ψ`. -/
theorem shiftHomAddEquiv_symm_comp {C : Type*} [Category* C] [Preadditive C] [HasShift C ℤ]
    [∀ m : ℤ, (shiftFunctor C m).Additive] (X Y Y' : C) (n : ℤ) (ψ : Y ⟶ Y')
    (f : X ⟶ Y⟦n⟧) :
    (shiftHomAddEquiv X Y' n).symm (f ≫ (shiftFunctor C n).map ψ) =
      (shiftHomAddEquiv X Y n).symm f ≫ ψ := by
  apply (shiftHomAddEquiv X Y' n).injective
  rw [AddEquiv.apply_symm_apply, shiftHomAddEquiv_comp, AddEquiv.apply_symm_apply]

/-! ### The corepresentation -/

variable {A : Type u} [Category.{v} A] [Abelian A] (T : A ⥤ AddCommGrpCat.{v}) [T.Additive]
  (Z : A) (e : preadditiveCoyoneda.obj (op Z) ≅ T)

section KInjective

variable [HasDerivedCategory.{w} A]

/-- `Z[0]⟦-n⟧` is concentrated in degrees `≤ n`. -/
instance isLE_singleFunctor_obj_shift (n : ℤ) :
    (((DerivedCategory.singleFunctor A 0).obj Z)⟦-n⟧).IsLE n :=
  DerivedCategory.TStructure.t.isLE_shift ((DerivedCategory.singleFunctor A 0).obj Z) 0 (-n) n
    (by omega)

/-- If `T` is corepresented by `Z`, then `T` applied degreewise to a K-injective complex `L` is the
complex `Hom(Z, L^•)`, whose degree-`n` cohomology is the group of morphisms `Z[0] ⟶ L⟦n⟧` in
the derived category. -/
def homologyMapHomologicalComplexAddEquiv (L : CochainComplex A ℤ) [L.IsKInjective] (n : ℤ) :
    ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).homology n ≃+
      ((DerivedCategory.singleFunctor A 0).obj Z ⟶ (DerivedCategory.Q.obj L)⟦n⟧) :=
  (HomologicalComplex.homologyMapIso
        ((NatIso.mapHomologicalComplex e.symm (ComplexShape.up ℤ)).app L)
        n).addCommGroupIsoToAddEquiv.trans
    (CochainComplex.coyonedaComplexHomologyEquiv Z L n)

end KInjective

section RightDerived

variable [EnoughInjectives A] [HasDerivedCategory.{w} A]
  [HasDerivedCategory.{w'} AddCommGrpCat.{v}]

/-- For an additive functor `T` corepresented by an object `Z` of an abelian category with enough
injectives, the degree-`n` cohomology of the right derived functor of `T` at an object `K` of the
bounded below derived category is the group of morphisms `Z[0] ⟶ K⟦n⟧` of the derived category.
-/
def rightDerivedHomologyAddEquiv (K : DerivedCategory.Plus A) (n : ℤ) :
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n).obj
        (T.rightDerivedFunctorPlus.obj K)) ≃+
      ((DerivedCategory.singleFunctor A 0).obj Z ⟶ (DerivedCategory.Plus.ι.obj K)⟦n⟧) :=
  corepresentedRightDerivedHomologyAddEquiv T Z e n K

/-- `rightDerivedHomologyAddEquiv` is natural in `K`: it carries the map induced on cohomology by
a morphism `φ` of the bounded below derived category to postcomposition with `φ⟦n⟧`. -/
theorem rightDerivedHomologyAddEquiv_naturality {K K' : DerivedCategory.Plus A} (φ : K ⟶ K')
    (n : ℤ) (x : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n).obj
      (T.rightDerivedFunctorPlus.obj K)) :
    rightDerivedHomologyAddEquiv T Z e K' n
        ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n).map
          (T.rightDerivedFunctorPlus.map φ) x) =
      rightDerivedHomologyAddEquiv T Z e K n x ≫
        (shiftFunctor (DerivedCategory A) n).map (DerivedCategory.Plus.ι.map φ) :=
  corepresentedRightDerivedHomologyAddEquiv_naturality T Z e n φ x

/-- `rightDerivedHomologyAddEquiv` read as morphisms out of a negative shift:
`H^n(RT(K)) ≃+ Hom_D(Z[0]⟦-n⟧, K)`. -/
def rightDerivedHomologyShiftAddEquiv (K : DerivedCategory.Plus A) (n : ℤ) :
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n).obj
        (T.rightDerivedFunctorPlus.obj K)) ≃+
      (((DerivedCategory.singleFunctor A 0).obj Z)⟦-n⟧ ⟶ DerivedCategory.Plus.ι.obj K) :=
  (rightDerivedHomologyAddEquiv T Z e K n).trans
    (shiftHomAddEquiv ((DerivedCategory.singleFunctor A 0).obj Z)
      (DerivedCategory.Plus.ι.obj K) n).symm

/-- `rightDerivedHomologyShiftAddEquiv` is natural in `K`: it carries the map induced on
cohomology by a morphism `φ` of the bounded below derived category to postcomposition with `φ`
itself. -/
theorem rightDerivedHomologyShiftAddEquiv_naturality {K K' : DerivedCategory.Plus A} (φ : K ⟶ K')
    (n : ℤ) (x : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n).obj
      (T.rightDerivedFunctorPlus.obj K)) :
    rightDerivedHomologyShiftAddEquiv T Z e K' n
        ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n).map
          (T.rightDerivedFunctorPlus.map φ) x) =
      rightDerivedHomologyShiftAddEquiv T Z e K n x ≫ DerivedCategory.Plus.ι.map φ := by
  dsimp only [rightDerivedHomologyShiftAddEquiv, AddEquiv.trans_apply]
  rw [rightDerivedHomologyAddEquiv_naturality T Z e φ n x, shiftHomAddEquiv_symm_comp]

end RightDerived

end Stacks.Cohomology.Corepresented

/-! ### The small Zariski site of a global crystalline situation -/

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open AlgebraicGeometry

variable (S : GlobalCrystallineSituation.{u})

/-- The constant sheaf `ℤ_X` on the small Zariski site of `X`, at the coefficient universe
`u + 1`. -/
abbrev zariskiIntegerSheaf : Sheaf (opensTopology S) AddCommGrpCat.{u + 1} :=
  (constantSheaf (opensTopology S) AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- `Γ(X_Zar, -)` is corepresented by the constant sheaf `ℤ_X`. -/
def zariskiGlobalSectionsCorepresentation :
    preadditiveCoyoneda.obj (op (zariskiIntegerSheaf S)) ≅ zariskiGlobalSections S :=
  (Stacks.Cohomology.GlobalSections.globalSectionsCorepresentation.{u + 1, u, u}
    (opensTopology S)).symm

section Derived

variable [HasDerivedCategory.{w} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]

/-- The object `ℤ_X[0]⟦-i⟧` of `D(Ab(X_Zar))`. -/
abbrev zariskiUnitShift (i : ℤ) :
    DerivedCategory (Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) :=
  ((DerivedCategory.singleFunctor (Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) 0).obj
    (zariskiIntegerSheaf S))⟦-i⟧

/-- `H^i(RΓ(X_Zar, K)) ≃+ Hom_{D(Ab(X_Zar))}(ℤ_X[0], K⟦i⟧)` for `K` an object of the bounded
below derived category of abelian sheaves on the small Zariski site. -/
def derivedZariskiGlobalSectionsHomologyAddEquiv
    (K : DerivedCategory.Plus (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})) (i : ℤ) :
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} i).obj
        ((derivedZariskiGlobalSectionsFunctor S).obj K)) ≃+
      ((DerivedCategory.singleFunctor (Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) 0).obj
          (zariskiIntegerSheaf S) ⟶ (DerivedCategory.Plus.ι.obj K)⟦i⟧) :=
  Stacks.Cohomology.Corepresented.rightDerivedHomologyAddEquiv (zariskiGlobalSections S)
    (zariskiIntegerSheaf S) (zariskiGlobalSectionsCorepresentation S) K i

/-- `H^i(RΓ(X_Zar, K)) ≃+ Hom_{D(Ab(X_Zar))}(ℤ_X[0]⟦-i⟧, K)` for `K` an object of the bounded
below derived category of abelian sheaves on the small Zariski site. -/
def derivedZariskiGlobalSectionsHomologyShiftAddEquiv
    (K : DerivedCategory.Plus (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})) (i : ℤ) :
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} i).obj
        ((derivedZariskiGlobalSectionsFunctor S).obj K)) ≃+
      (zariskiUnitShift S i ⟶ DerivedCategory.Plus.ι.obj K) :=
  Stacks.Cohomology.Corepresented.rightDerivedHomologyShiftAddEquiv (zariskiGlobalSections S)
    (zariskiIntegerSheaf S) (zariskiGlobalSectionsCorepresentation S) K i

/-- The identification `H^i(RΓ(X_Zar, K)) ≃+ Hom_{D(Ab(X_Zar))}(ℤ_X[0], K⟦i⟧)` is natural in
`K`: it carries `H^i(RΓ(X_Zar, φ))` to postcomposition with `φ⟦i⟧`. -/
theorem derivedZariskiGlobalSectionsHomologyAddEquiv_naturality
    {K K' : DerivedCategory.Plus (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})} (φ : K ⟶ K')
    (i : ℤ) (x : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} i).obj
      ((derivedZariskiGlobalSectionsFunctor S).obj K)) :
    derivedZariskiGlobalSectionsHomologyAddEquiv S K' i
        ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} i).map
          ((derivedZariskiGlobalSectionsFunctor S).map φ) x) =
      derivedZariskiGlobalSectionsHomologyAddEquiv S K i x ≫
        (shiftFunctor (DerivedCategory (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})) i).map
          (DerivedCategory.Plus.ι.map φ) :=
  Stacks.Cohomology.Corepresented.rightDerivedHomologyAddEquiv_naturality
    (zariskiGlobalSections S) (zariskiIntegerSheaf S)
    (zariskiGlobalSectionsCorepresentation S) φ i x

/-- The identification `H^i(RΓ(X_Zar, K)) ≃+ Hom_{D(Ab(X_Zar))}(ℤ_X[0]⟦-i⟧, K)` is natural in
`K`: it carries `H^i(RΓ(X_Zar, φ))` to postcomposition with `φ` itself. -/
theorem derivedZariskiGlobalSectionsHomologyShiftAddEquiv_naturality
    {K K' : DerivedCategory.Plus (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})} (φ : K ⟶ K')
    (i : ℤ) (x : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} i).obj
      ((derivedZariskiGlobalSectionsFunctor S).obj K)) :
    derivedZariskiGlobalSectionsHomologyShiftAddEquiv S K' i
        ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} i).map
          ((derivedZariskiGlobalSectionsFunctor S).map φ) x) =
      derivedZariskiGlobalSectionsHomologyShiftAddEquiv S K i x ≫
        DerivedCategory.Plus.ι.map φ :=
  Stacks.Cohomology.Corepresented.rightDerivedHomologyShiftAddEquiv_naturality
    (zariskiGlobalSections S) (zariskiIntegerSheaf S)
    (zariskiGlobalSectionsCorepresentation S) φ i x

end Derived

end Crystalline.GlobalCrystallineSituation.SmallSite

end
