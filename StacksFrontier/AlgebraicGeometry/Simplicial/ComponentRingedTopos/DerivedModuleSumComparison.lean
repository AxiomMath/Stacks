module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianDerivedModuleOfModuleSystem
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleLowerShriekLeftDerived
public import StacksFrontier.CategoryTheory.Localization.MapHomotopyCategoryAdjunctionCounit

/-!
# The componentwise direct-sum formula for the left derived lower shriek, without flatness

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of commutative rings on its
total site. For simplicial degrees `n` and `m` and an object `X` of `D(O_n)` there is a canonical
map
`⨁_{φ : [n] ⟶ [m]} Lf_φ^* X ⟶ g_m^* Lg_{n!} X`
whose `φ`th component is the unit of `Lg_{n!} ⊣ g_n^*` carried along `Lf_φ^*`, followed by the
derived transition `K(φ)` of Stacks 0D9P at `K = Lg_{n!} X`. This file proves that it is an
isomorphism, with no flatness hypothesis on the structure-sheaf transitions: this is the
derived form of the componentwise direct-sum formula of Stacks 0D72 (6), with its summand
inclusions identified.

Every object of `D(O_n)` is the image of a K-flat complex with flat terms, on which `Lg_{n!}` and
the `Lf_φ^*` are computed degreewise. There the canonical map becomes the image in the derived
category of the sheaf-level direct-sum formula, whose summand inclusions are the canonical maps
by `CategoryTheory.SimplicialSiteSituation.moduleSumFormulaLegEq`.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.derivedModuleSumComparison`: the canonical map.

## Main results

* `CategoryTheory.NatTrans.isIso_biproduct_desc_map_mapHomologicalComplex`: applying a finite
  direct sum of functors degreewise to a complex gives the direct sum of the complexes.
* `CategoryTheory.SimplicialSiteSituation.isIso_derivedModuleSumComparison`: **the canonical map
  is an isomorphism.**

## References

* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 0D9P](https://stacks.math.columbia.edu/tag/0D9P)
* [Stacks Project, Tag 0D9T](https://stacks.math.columbia.edu/tag/0D9T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward

universe u

namespace CategoryTheory.NatTrans

variable {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
  {ι : Type*} {c : ComplexShape ι} {J : Type} [Finite J] {F : J → A ⥤ B}
  [hF : ∀ j, (F j).Additive] [HasBiproduct F] {G : A ⥤ B} [hG : G.Additive]
  (l : ∀ j, F j ⟶ G) (P : HomologicalComplex A c)
  {D : Type*} [Category* D] [Preadditive D] [HasFiniteBiproducts D]
  (q : HomologicalComplex B c ⥤ D) [hq : q.Additive]

/-- **A finite direct sum decomposition of a functor survives applying it degreewise to a
complex, and then any additive functor.** If the transformations `l_j : F_j ⟶ G` exhibit `G` as
the direct sum of the `F_j`, then the images under `q` of the induced maps of complexes exhibit
`q(G(P))` as the direct sum of the `q(F_j(P))`. -/
theorem isIso_biproduct_desc_map_mapHomologicalComplex (hl : IsIso (biproduct.desc l)) :
    IsIso (biproduct.desc fun j => q.map ((NatTrans.mapHomologicalComplex (l j) c).app P)) := by
  classical
  have := Fintype.ofFinite J
  have hι : ∀ j, l j ≫ inv (biproduct.desc l) = biproduct.ι F j := fun j =>
    (IsIso.comp_inv_eq _).2 (biproduct.ι_desc l j).symm
  refine ⟨biproduct.lift fun j => q.map ((NatTrans.mapHomologicalComplex
    (inv (biproduct.desc l) ≫ biproduct.π F j) c).app P), ?_, ?_⟩
  · refine biproduct.hom_ext' _ _ fun i => biproduct.hom_ext _ _ fun j => ?_
    simp only [biproduct.ι_desc_assoc, Category.assoc, biproduct.lift_π, Category.id_comp,
      ← q.map_comp, ← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp]
    rw [← Category.assoc (l i), hι i]
    obtain rfl | h := eq_or_ne i j
    · simp only [biproduct.ι_π_self, NatTrans.mapHomologicalComplex_id, NatTrans.id_app,
        q.map_id]
    · rw [biproduct.ι_π_ne _ h, biproduct.ι_π_ne _ h]
      have h0 : (NatTrans.mapHomologicalComplex (0 : F i ⟶ F j) c).app P = 0 :=
        HomologicalComplex.hom_ext _ _ fun _ => rfl
      rw [h0, q.map_zero]
  · have hsum : (∑ j, (NatTrans.mapHomologicalComplex
        (inv (biproduct.desc l) ≫ biproduct.π F j) c).app P ≫
        (NatTrans.mapHomologicalComplex (l j) c).app P) = 𝟙 _ := by
      refine HomologicalComplex.hom_ext _ _ fun k => ?_
      rw [← HomologicalComplex.eval_map, Functor.map_sum]
      simp only [HomologicalComplex.eval_map, HomologicalComplex.comp_f,
        NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.id_f]
      have h := congr_app (show (∑ j, (inv (biproduct.desc l) ≫ biproduct.π F j) ≫ l j) = 𝟙 G by
        simp only [Category.assoc, ← Preadditive.comp_sum, ← biproduct.desc_eq,
          IsIso.inv_hom_id]) (P.X k)
      simp only [NatTrans.app_sum, NatTrans.comp_app, NatTrans.id_app, Category.assoc] at h
      simp only [NatTrans.comp_app, Category.assoc]
      exact h
    rw [biproduct.lift_desc, ← q.map_id, ← hsum, Functor.map_sum]
    simp only [q.map_comp]

end CategoryTheory.NatTrans

namespace CategoryTheory.Limits

/-- A summand inclusion, followed by a map of direct sums and a map out of the direct sum. -/
theorem biproduct_ι_map_desc {C : Type*} [Category* C] [HasZeroMorphisms C] {J : Type*}
    {f g : J → C} [HasBiproduct f] [HasBiproduct g] {Z : C} (p : ∀ j, f j ⟶ g j)
    (h : ∀ j, g j ⟶ Z) (j : J) :
    biproduct.ι f j ≫ biproduct.map p ≫ biproduct.desc h = p j ≫ h j := by
  rw [biproduct.ι_map_assoc, biproduct.ι_desc]

/-- The diagram chase behind the components of the derived direct-sum comparison, with every
morphism a variable. -/
theorem sumComparison_chase {C : Type*} [Category* C] {A B₁ B₂ C₁ C₂ E Q₁ Q₂ Q₃ : C}
    {Lη : A ⟶ B₁} {τ₁ : B₁ ⟶ C₁} {Rα : C₁ ⟶ C₂} {βh : C₂ ⟶ E} {Lα : B₁ ⟶ B₂} {τ₂ : B₂ ⟶ C₂}
    {Lu : A ⟶ Q₁} {Lbi : Q₁ ⟶ B₂} {Lbh : B₂ ⟶ Q₁} {c₂ : Q₁ ⟶ Q₂} {Qτ : Q₂ ⟶ E}
    {βi : E ⟶ C₂} {c₁ : A ⟶ Q₃} {Qf : Q₃ ⟶ Q₂} {Ql : Q₃ ⟶ E}
    (hnat : Lα ≫ τ₂ = τ₁ ≫ Rα) (hunit : Lη ≫ Lα = Lu ≫ Lbi)
    (hτ : τ₂ = Lbh ≫ c₂ ≫ Qτ ≫ βi) (hb₁ : Lbi ≫ Lbh = 𝟙 _) (hb₂ : βi ≫ βh = 𝟙 _)
    (hcmp : Lu ≫ c₂ = c₁ ≫ Qf) (hK : Qf ≫ Qτ = Ql) :
    Lη ≫ τ₁ ≫ Rα ≫ βh = c₁ ≫ Ql := by
  rw [← reassoc_of% hnat, reassoc_of% hunit, hτ]
  simp only [Category.assoc, reassoc_of% hb₁, hb₂, Category.comp_id]
  rw [reassoc_of% hcmp, hK]

end CategoryTheory.Limits

namespace CategoryTheory.SimplicialSiteSituation

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- The lower shriek functor of modules on the `n`th component is additive. -/
instance componentModuleLowerShriek_totalRingSheaf_additive (n : SimplexCategory) :
    (S.componentModuleLowerShriek (S.totalRingSheaf O) n).Additive :=
  (S.componentModulesLowerShriekAdjunction O n).left_adjoint_additive

/-- The lower shriek functor on the `n`th component followed by restriction to the `m`th component
is additive. -/
instance componentModuleLowerShriek_comp_restriction_additive (n m : SimplexCategory) :
    (S.componentModuleLowerShriek (S.totalRingSheaf O) n ⋙
      S.componentModuleRestriction (S.totalRingSheaf O) m).Additive :=
  inferInstanceAs (S.componentModulesLowerShriek O n ⋙ S.componentModulesRestriction O m).Additive

/-- The lower shriek functor on the `n`th component followed by restriction to the `m`th component
is additive, for the tensor ring sheaf of `O`. -/
instance componentModuleLowerShriek_comp_restriction_additive' (n m : SimplexCategory) :
    (S.componentModuleLowerShriek (Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)
        n ⋙
      S.componentModuleRestriction
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O) m).Additive :=
  inferInstanceAs (S.componentModuleLowerShriek (S.totalRingSheaf O) n ⋙
      S.componentModuleRestriction (S.totalRingSheaf O) m).Additive

/-- The pullback of modules along the transition morphism of a simplex map `φ` is additive. -/
instance transitionPullbackModules'_additive {n m : SimplexCategory} (φ : n ⟶ m) :
    (S.transitionPullbackModules' O φ).Additive :=
  inferInstanceAs ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules).Additive

/-- **The canonical map `⨁_{φ : [n] ⟶ [m]} Lf_φ^* X ⟶ g_m^* Lg_{n!} X`**: its `φ`th component is
the unit of `Lg_{n!} ⊣ g_n^*` carried along `Lf_φ^*`, followed by the derived transition of
Stacks 0D9P at `Lg_{n!} X`. -/
def derivedModuleSumComparison (n m : SimplexCategory)
    (X : DerivedCategory (S.componentRingedTopos O n).Modules) :
    letI : Fintype (n ⟶ m) := Fintype.ofFinite (n ⟶ m)
    ⨁ (fun φ : n ⟶ m => (S.derivedTransitionPullback O φ).obj X) ⟶
      (S.derivedComponentModuleRestriction O m).obj
        ((S.componentModuleLowerShriekLeftDerived O n).obj X) :=
  letI : Fintype (n ⟶ m) := Fintype.ofFinite (n ⟶ m)
  biproduct.desc fun φ => (S.derivedTransitionPullback O φ).map
      ((S.componentModuleLowerShriekLeftDerivedAdjunction O n).unit.app X) ≫
    (S.derivedComponentModuleTransition O φ).app
      ((S.componentModuleLowerShriekLeftDerived O n).obj X)

/-- The `φ`th component of the canonical map. -/
theorem ι_derivedModuleSumComparison {n m : SimplexCategory} (φ : n ⟶ m)
    (X : DerivedCategory (S.componentRingedTopos O n).Modules) :
    letI : Fintype (n ⟶ m) := Fintype.ofFinite (n ⟶ m)
    biproduct.ι (fun φ : n ⟶ m => (S.derivedTransitionPullback O φ).obj X) φ ≫
        S.derivedModuleSumComparison O n m X =
      (S.derivedTransitionPullback O φ).map
          ((S.componentModuleLowerShriekLeftDerivedAdjunction O n).unit.app X) ≫
        (S.derivedComponentModuleTransition O φ).app
          ((S.componentModuleLowerShriekLeftDerived O n).obj X) :=
  biproduct.ι_desc _ _

/-- The canonical map is natural in `X`. -/
theorem derivedModuleSumComparison_naturality (n m : SimplexCategory)
    {X X' : DerivedCategory (S.componentRingedTopos O n).Modules} (f : X ⟶ X') :
    letI : Fintype (n ⟶ m) := Fintype.ofFinite (n ⟶ m)
    biproduct.map (fun φ : n ⟶ m => (S.derivedTransitionPullback O φ).map f) ≫
        S.derivedModuleSumComparison O n m X' =
      S.derivedModuleSumComparison O n m X ≫
        (S.derivedComponentModuleRestriction O m).map
          ((S.componentModuleLowerShriekLeftDerived O n).map f) := by
  let : Fintype (n ⟶ m) := Fintype.ofFinite (n ⟶ m)
  refine biproduct.hom_ext' _ _ fun φ => ?_
  rw [biproduct.ι_map_assoc, ι_derivedModuleSumComparison, ← Category.assoc (biproduct.ι _ φ),
    ι_derivedModuleSumComparison, Category.assoc, ← Functor.map_comp_assoc,
    ← (S.componentModuleLowerShriekLeftDerivedAdjunction O n).unit_naturality f,
    Functor.map_comp, Category.assoc]
  exact congrArg _ ((S.derivedComponentModuleTransition O φ).naturality
    ((S.componentModuleLowerShriekLeftDerived O n).map f))

/-- The canonical map attached to `φ` on sheaves of modules, applied degreewise to a complex:
the unit of `g_{n!} ⊣ g_n^*` carried along `f_φ^*`, followed by the pullback transition. -/
abbrev moduleSumFormulaLegComplex {n m : SimplexCategory} (φ : n ⟶ m)
    (P : CochainComplex (S.componentRingedTopos O n).Modules ℤ) :
    ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P ⟶
      ((S.componentModulesRestriction O m).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((S.componentModulesLowerShriek O n).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.mapHomologicalComplex
      (ComplexShape.up ℤ)).map
    (((S.componentModulesLowerShriekAdjunction O n).mapHomologicalComplexAdjunction
      (ComplexShape.up ℤ)).unit.app P) ≫
    (NatTrans.mapHomologicalComplex (S.componentModulesTransition O φ) (ComplexShape.up ℤ)).app
      (((S.componentModulesLowerShriek O n).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)

/-- **The degreewise legs exhibit the direct sum, after any additive functor.** For every complex
`P` of `O_n`-modules and every additive functor `q` out of complexes of `O_m`-modules, the map
out of the direct sum of the `q(f_φ^*P)` whose components are the images of the degreewise
canonical maps is an isomorphism: the canonical maps are the summand inclusions of the
sheaf-level direct-sum formula of Stacks 0D72 (6), by
`CategoryTheory.SimplicialSiteSituation.moduleSumFormulaLegEq`. -/
theorem isIso_biproduct_desc_map_moduleSumFormulaLegComplex (n m : SimplexCategory)
    (P : CochainComplex (S.componentRingedTopos O n).Modules ℤ)
    {D : Type*} [Category* D] [Preadditive D] [HasFiniteBiproducts D]
    (q : CochainComplex (S.componentRingedTopos O m).Modules ℤ ⥤ D) [hq : q.Additive] :
    letI : Fintype (n ⟶ m) := Fintype.ofFinite (n ⟶ m)
    IsIso (biproduct.desc fun φ : n ⟶ m => q.map (S.moduleSumFormulaLegComplex O φ P)) := by
  let : Fintype (n ⟶ m) := Fintype.ofFinite (n ⟶ m)
  let : HasFiniteBiproducts
      (SheafOfModules.{u} (S.componentRingSheaf
          (Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O) n) ⥤
        SheafOfModules.{u} (S.componentRingSheaf
          (Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O) m)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have hfun : biproduct.desc (fun φ : n ⟶ m => S.moduleSumFormulaLeg O φ) =
      (biproduct.isoCoproduct _).hom ≫ (S.moduleSumFormula O n m).inv := by
    refine biproduct.hom_ext' _ _ fun φ => ?_
    rw [biproduct.ι_desc, biproduct.isoCoproduct_hom]
    exact ((S.moduleSumFormulaLegEq O) φ).symm.trans
      ((congrArg (· ≫ (S.moduleSumFormula O n m).inv) (biproduct.ι_desc _ _).symm).trans
        (Category.assoc _ _ _))
  have hfunIso : IsIso (biproduct.desc (fun φ : n ⟶ m => S.moduleSumFormulaLeg O φ)) := by
    rw [hfun]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _)
      (Iso.isIso_inv (S.moduleSumFormula O n m))
  exact NatTrans.isIso_biproduct_desc_map_mapHomologicalComplex
    (hF := fun φ => S.transitionPullbackModules'_additive O φ)
    (hG := S.componentModuleLowerShriek_comp_restriction_additive O n m) (hq := hq)
    (fun φ : n ⟶ m => S.moduleSumFormulaLeg O φ) P q hfunIso

/-- **The `φ`th component of the canonical map at a complex**, followed by the comparison of
`Lg_{n!}` and of the derived restriction: it is the comparison of `Lf_φ^*` followed by the image
of the degreewise canonical map attached to `φ`. -/
theorem ι_derivedModuleSumComparison_comp {n m : SimplexCategory} (φ : n ⟶ m)
    (P : CochainComplex (S.componentRingedTopos O n).Modules ℤ) :
    letI : Fintype (n ⟶ m) := Fintype.ofFinite (n ⟶ m)
    biproduct.ι (fun φ : n ⟶ m => (S.derivedTransitionPullback O φ).obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) φ ≫
        S.derivedModuleSumComparison O n m
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≫
        (S.derivedComponentModuleRestriction O m).map
          ((S.componentModuleLowerShriekLeftDerivedComparison O n).app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≫
        (S.componentModulesRestriction O m).mapDerivedCategoryFactorsh.hom.app
          (((S.componentModulesLowerShriek O n).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) =
      (S.derivedTransitionComparison O φ).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          (S.moduleSumFormulaLegComplex O φ P)) := by
  let : Fintype (n ⟶ m) := Fintype.ofFinite (n ⟶ m)
  have hτ := liftedTransition_app_q (S.componentModulesRestriction O n).mapDerivedCategoryFactorsh
    (S.derivedTransitionComparison O φ)
    (S.componentModulesRestriction O m).mapDerivedCategoryFactorsh
    (mapHomotopyCategoryTransition (ComplexShape.up ℤ) (S.componentModulesRestriction O n)
      (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules
      (S.componentModulesRestriction O m) (S.componentModulesTransition O φ))
    (HomotopyCategory.quasiIso ((S.totalRingedTopos O).Modules) (ComplexShape.up ℤ))
    (((S.componentModulesLowerShriek O n).mapHomotopyCategory (ComplexShape.up ℤ)).obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))
  have hnat := (S.derivedComponentModuleTransition O φ).naturality
    ((S.componentModuleLowerShriekLeftDerivedComparison O n).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))
  have hunit := S.componentModuleLowerShriekLeftDerivedAdjunction_unit_fac O n
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)
  have hcmp := (S.derivedTransitionComparison O φ).naturality
    (((S.componentModulesLowerShriekAdjunction O n).mapHomotopyCategoryAdjunction
      (ComplexShape.up ℤ)).unit.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))
  have hK : ((pullbackMapHomotopy (S.transitionRingedToposHom O φ)).map
      (((S.componentModulesLowerShriekAdjunction O n).mapHomotopyCategoryAdjunction
        (ComplexShape.up ℤ)).unit.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≫
      (mapHomotopyCategoryTransition (ComplexShape.up ℤ) (S.componentModulesRestriction O n)
        (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules
        (S.componentModulesRestriction O m) (S.componentModulesTransition O φ)).app
        (((S.componentModulesLowerShriek O n).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (S.moduleSumFormulaLegComplex O φ P) := by
    rw [mapHomotopyCategoryTransition_app,
      Adjunction.mapHomotopyCategoryAdjunction_unit_app_quotient]
    exact ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_comp _ _).symm
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at hnat hcmp
  rw [← Category.assoc, ι_derivedModuleSumComparison, Category.assoc]
  refine sumComparison_chase (Lbi := (S.derivedTransitionPullback O φ).map
      ((S.componentModulesRestriction O n).mapDerivedCategoryFactorsh.inv.app
        (((S.componentModulesLowerShriek O n).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))))
    hnat ?_ hτ ?_ (Iso.inv_hom_id_app _ _) hcmp ?_
  · exact ((S.derivedTransitionPullback O φ).map_comp _ _).symm.trans
      ((congrArg (S.derivedTransitionPullback O φ).map hunit).trans (Functor.map_comp _ _ _))
  · rw [← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
  · rw [← DerivedCategory.Qh.map_comp]
    exact congrArg DerivedCategory.Qh.map hK

/-- **The canonical map `⨁_{φ : [n] ⟶ [m]} Lf_φ^* X ⟶ g_m^* Lg_{n!} X` is an isomorphism**, for
every object `X` of `D(O_n)` and with no flatness hypothesis: the derived form of the
componentwise direct-sum formula of Stacks 0D72 (6), with its summand inclusions identified. -/
theorem isIso_derivedModuleSumComparison (n m : SimplexCategory)
    (X : DerivedCategory (S.componentRingedTopos O n).Modules) :
    IsIso (S.derivedModuleSumComparison O n m X) := by
  let : Fintype (n ⟶ m) := Fintype.ofFinite (n ⟶ m)
  have key : ∀ P : CochainComplex (S.componentRingedTopos O n).Modules ℤ,
      S.componentKFlat O n ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) →
      IsIso (S.derivedModuleSumComparison O n m
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) := by
    intro P hP
    have hα := S.isIso_componentModuleLowerShriekLeftDerivedComparison_app O n _ hP
    have hc : ∀ φ : n ⟶ m, IsIso ((S.derivedTransitionComparison O φ).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) := fun φ =>
      S.isIso_derivedTransitionComparison_app O φ _ hP
    have hleg := S.isIso_biproduct_desc_map_moduleSumFormulaLegComplex O n m P
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    have h3 : IsIso ((S.derivedComponentModuleRestriction O m).map
        ((S.componentModuleLowerShriekLeftDerivedComparison O n).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) := Functor.map_isIso _ _
    have h4 := @IsIso.comp_isIso _ _ _ _ _ _ _ h3
      (inferInstance : IsIso
        ((S.componentModulesRestriction O m).mapDerivedCategoryFactorsh.hom.app
          (((S.componentModulesLowerShriek O n).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))))
    refine @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ h4 ?_
    have heq : S.derivedModuleSumComparison O n m
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≫
          (S.derivedComponentModuleRestriction O m).map
            ((S.componentModuleLowerShriekLeftDerivedComparison O n).app
              ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≫
          (S.componentModulesRestriction O m).mapDerivedCategoryFactorsh.hom.app
            (((S.componentModulesLowerShriek O n).mapHomotopyCategory (ComplexShape.up ℤ)).obj
              ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) =
        (biproduct.mapIso fun φ : n ⟶ m => asIso ((S.derivedTransitionComparison O φ).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))).hom ≫
          biproduct.desc fun φ : n ⟶ m =>
            (HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map
              (S.moduleSumFormulaLegComplex O φ P) := by
      refine biproduct.hom_ext' _ _ fun φ => ?_
      rw [S.ι_derivedModuleSumComparison_comp O φ P, biproduct.mapIso_hom]
      refine Eq.trans ?_ (biproduct_ι_map_desc
        (fun φ : n ⟶ m => (asIso ((S.derivedTransitionComparison O φ).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))).hom)
        (fun φ : n ⟶ m => (HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).map (S.moduleSumFormulaLegComplex O φ P)) φ).symm
      rfl
    rw [heq]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance hleg
  obtain ⟨P', hP', s, hs⟩ :=
    S.hasResolutions_componentKFlat O n (DerivedCategory.Qh.objPreimage X)
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P'
  have hsiso : IsIso (DerivedCategory.Qh.map s) :=
    Localization.inverts DerivedCategory.Qh _ s hs
  let e : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) ≅ X :=
    asIso (DerivedCategory.Qh.map s) ≪≫ DerivedCategory.Qh.objObjPreimageIso X
  have := key P hP'
  have h1 : IsIso (biproduct.map (fun φ : n ⟶ m => (S.derivedTransitionPullback O φ).map e.hom) ≫
      S.derivedModuleSumComparison O n m X) := by
    rw [S.derivedModuleSumComparison_naturality O n m e.hom]
    infer_instance
  have : IsIso (biproduct.map fun φ : n ⟶ m => (S.derivedTransitionPullback O φ).map e.hom) :=
    inferInstanceAs (IsIso (biproduct.mapIso fun φ : n ⟶ m =>
      (S.derivedTransitionPullback O φ).mapIso e).hom)
  exact IsIso.of_isIso_comp_left
    (biproduct.map fun φ : n ⟶ m => (S.derivedTransitionPullback O φ).map e.hom) _

end CategoryTheory.SimplicialSiteSituation

end
