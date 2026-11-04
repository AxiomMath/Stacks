module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.SchemeToRing

/-!
# The map of Stacks 0DJ7 at a map of complexes, on stalks

For complexes `𝒩` on `X` and `𝒵` on `X'` and a map of complexes `g'^*𝒩 ⟶ 𝒵`, the map of
Stacks 0DJ7 at the composite `L(g')^*𝒩 ⟶ g'^*𝒩 ⟶ 𝒵` is invertible exactly when the ring-level map
of Stacks 0DJ7 at the stalk complexes is, the stalk of `g'^*𝒩` being identified with the base
change of the stalk of `𝒩`.

## Main results

* `AlgebraicGeometry.isIso_baseChangeCohomologyMap_complex_iff`: the base change map in degree `n`
  at the composite `L(g')^*𝒩 ⟶ g'^*𝒩 ⟶ 𝒵` is invertible at `x'` if and only if the ring-level
  base change map of the stalk complexes is invertible in degree `n`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct ChangeOfRings
open RingTheory.TorIndependence

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
  (w : g' ≫ f = f' ≫ g)

/-- If `a ≫ b ≫ c = s ≫ e₁.hom ≫ e₂.hom` for isomorphisms `e₁` and `e₂`, then
`s = a ≫ b ≫ c ≫ e₂.inv ≫ e₁.inv`. -/
theorem eq_comp_inv_inv_of_eq {C : Type*} [Category C] {X Y Z W U V : C} (s : X ⟶ Y)
    (e₁ : Y ≅ Z) (e₂ : Z ≅ W) (a : X ⟶ U) (b : U ⟶ V) (c : V ⟶ W)
    (h : a ≫ b ≫ c = s ≫ e₁.hom ≫ e₂.hom) : s = a ≫ b ≫ c ≫ e₂.inv ≫ e₁.inv := by
  rw [← Category.assoc b, ← Category.assoc a, h]; simp

/-- The characterization of the derived stalk comparison, solved for the stalk of the
comparison of the derived pullback with the degreewise pullback. -/
theorem derivedStalkFunctor_map_pullbackComparisonOnComplex (x : X')
    (P : CochainComplex X.Modules ℤ) :
    (derivedStalkFunctor x).map (pullbackComparisonOnComplex g' P) =
      (derivedPullbackStalkIso g' x).hom.app (DerivedCategory.Q.obj P) ≫
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (g'.stalkMap x).hom).functor.map ((Stacks.ModuleSkyscraper.modulesStalkFunctor X
            (g' x)).mapDerivedCategoryFactors.hom.app P) ≫
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (g'.stalkMap x).hom).comparison.app (((Stacks.ModuleSkyscraper.modulesStalkFunctor X
            (g' x)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (Stacks.ModuleSkyscraper.pullbackStalkIso g' x) (ComplexShape.up ℤ)).hom.app P) ≫
        (Stacks.ModuleSkyscraper.modulesStalkFunctor X' x).mapDerivedCategoryFactors.inv.app
          (((Scheme.Modules.pullback g').mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
  have C := derivedPullbackStalkIso_comp_comparison g' x P
  exact eq_comp_inv_inv_of_eq _ ((Stacks.ModuleSkyscraper.modulesStalkFunctor X'
    x).mapDerivedCategoryFactors.app (((Scheme.Modules.pullback g').mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P))
    (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
      (Stacks.ModuleSkyscraper.pullbackStalkIso g' x).symm (ComplexShape.up ℤ)).app P)) _ _ _ C

/-- Given factorizations `spa = sp ≫ sa`, `qpa = qp ≫ qa` and
`sp = ιh ≫ Tf ≫ cmp ≫ qp ≫ fi`, retractions `ιi ≫ ιh = 𝟙` and `Tfi ≫ Tf = 𝟙`, and a commuting
square `fi ≫ sa = qa ≫ fi'`, the composites `Tfi ≫ ιi ≫ spa` and `(cmp ≫ qpa) ≫ fi'` agree. -/
theorem stalk_chase {C : Type*} [Category C] {P₀ P₁ P₂ P₃ P₄ Q₁ Q₂ Q₃ : C}
    (Tfi : P₀ ⟶ P₁) (ιi : P₁ ⟶ P₂) (ιh : P₂ ⟶ P₁) (Tf : P₁ ⟶ P₀) (sp : P₂ ⟶ P₃) (sa : P₃ ⟶ P₄)
    (spa : P₂ ⟶ P₄) (cmp : P₀ ⟶ Q₁) (qp : Q₁ ⟶ Q₂) (fi : Q₂ ⟶ P₃) (qa : Q₂ ⟶ Q₃) (qpa : Q₁ ⟶ Q₃)
    (fi' : Q₃ ⟶ P₄) (hspa : spa = sp ≫ sa) (hqpa : qpa = qp ≫ qa)
    (hst : sp = ιh ≫ Tf ≫ cmp ≫ qp ≫ fi) (h1 : ιi ≫ ιh = 𝟙 _) (h2 : Tfi ≫ Tf = 𝟙 _)
    (hn : fi ≫ sa = qa ≫ fi') :
    Tfi ≫ ιi ≫ spa = (cmp ≫ qpa) ≫ fi' := by
  rw [hspa, hqpa, hst]
  simp only [Category.assoc, hn, reassoc_of% h1, reassoc_of% h2]

/-- **The map of Stacks 0DJ7 at a degreewise pullback followed by a map of complexes**, read on
the stalk complexes. -/
theorem isIso_baseChangeCohomologyMap_complex_iff (𝒩 : CochainComplex X.Modules ℤ)
    (𝒵 : CochainComplex X'.Modules ℤ)
    (a : ((Scheme.Modules.pullback g').mapHomologicalComplex (ComplexShape.up ℤ)).obj 𝒩 ⟶ 𝒵)
    (x' : X') (n : ℤ) :
    letI : Algebra (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x')) :=
      ((f.stalkMap (g' x')).hom).toAlgebra
    letI : Algebra (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x')) :=
      (baseStalkMap f g f' g' w x').toAlgebra
    letI : Algebra (S.presheaf.stalk (f (g' x'))) (X'.presheaf.stalk x') :=
      (((g'.stalkMap x').hom).comp ((f.stalkMap (g' x')).hom)).toAlgebra
    letI : Algebra (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x') :=
      ((g'.stalkMap x').hom).toAlgebra
    letI : Algebra (S'.presheaf.stalk (f' x')) (X'.presheaf.stalk x') :=
      ((f'.stalkMap x').hom).toAlgebra
    letI : IsScalarTower (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x'))
        (X'.presheaf.stalk x') := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x'))
        (X'.presheaf.stalk x') := IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' w x')
    IsIso (baseChangeCohomologyMap f g f' g' w (DerivedCategory.Q.obj 𝒩) (DerivedCategory.Q.obj 𝒵)
        (pullbackComparisonOnComplex g' 𝒩 ≫ DerivedCategory.Q.map a) x' n) ↔
      IsIso (ringBaseChangeCohomologyMap (R := S.presheaf.stalk (f (g' x')))
        (R' := S'.presheaf.stalk (f' x'))
        (DerivedCategory.Q.obj (((Stacks.ModuleSkyscraper.modulesStalkFunctor X
          (g' x')).mapHomologicalComplex (ComplexShape.up ℤ)).obj 𝒩))
        (DerivedCategory.Q.obj (((Stacks.ModuleSkyscraper.modulesStalkFunctor X'
          x').mapHomologicalComplex (ComplexShape.up ℤ)).obj 𝒵))
        (alphaH _ _ _ ≫ DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (Stacks.ModuleSkyscraper.pullbackStalkIso g' x') (ComplexShape.up ℤ)).hom.app 𝒩 ≫
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor X' x').mapHomologicalComplex
            (ComplexShape.up ℤ)).map a)) n) := by
  let : Algebra (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x')) :=
    ((f.stalkMap (g' x')).hom).toAlgebra
  let : Algebra (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x')) :=
    (baseStalkMap f g f' g' w x').toAlgebra
  let : Algebra (S.presheaf.stalk (f (g' x'))) (X'.presheaf.stalk x') :=
    (((g'.stalkMap x').hom).comp ((f.stalkMap (g' x')).hom)).toAlgebra
  let : Algebra (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x') :=
    ((g'.stalkMap x').hom).toAlgebra
  let : Algebra (S'.presheaf.stalk (f' x')) (X'.presheaf.stalk x') :=
    ((f'.stalkMap x').hom).toAlgebra
  let : IsScalarTower (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x'))
      (X'.presheaf.stalk x') := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x'))
      (X'.presheaf.stalk x') := IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' w x')
  refine Iff.trans ?_ (isIso_choose_ringBaseChangeCohomologyMap_iff _ _ _ n)
  refine (isIso_chosenBaseChangeMap_iff_of_iso
    ((Stacks.ModuleSkyscraper.modulesStalkFunctor X (g' x')).mapDerivedCategoryFactors.app 𝒩).symm
    ((Stacks.ModuleSkyscraper.modulesStalkFunctor X' x').mapDerivedCategoryFactors.app 𝒵).symm
    _ ((derivedPullbackStalkIso g' x').inv.app (DerivedCategory.Q.obj 𝒩) ≫
      (derivedStalkFunctor x').map (pullbackComparisonOnComplex g' 𝒩 ≫ DerivedCategory.Q.map a))
    ?_ n).symm
  refine stalk_chase _ _ ((derivedPullbackStalkIso g' x').hom.app (DerivedCategory.Q.obj 𝒩))
    _ _ _ _ _ _ _ _ _ _ (Functor.map_comp _ _ _) (Functor.map_comp _ _ _)
    (derivedStalkFunctor_map_pullbackComparisonOnComplex g' x' 𝒩) (Iso.inv_hom_id_app _ _) ?_ ?_
  · exact (Functor.map_comp _ _ _).symm.trans ((congrArg _ (Iso.inv_hom_id_app _ _)).trans
      (CategoryTheory.Functor.map_id _ _))
  · exact
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor X' x').mapDerivedCategoryFactors.inv.naturality
        a).symm

end AlgebraicGeometry
