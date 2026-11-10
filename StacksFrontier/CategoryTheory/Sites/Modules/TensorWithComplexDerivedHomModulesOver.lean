module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModuleRestrict
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedHom
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical map of Tag 0CS6 over a base ring

Let `(C, O)` be a ringed site, let `R` be a commutative ring with a sheaf of commutative
`R`-algebra structures on `O` (an `AlgebraicGeometry.RingedSite.ScalarSections` instance), let
`K` be a complex of `O`-modules and let `(E, d) = Hom_{Comp^dg(O)}(K, K)` be its endomorphism
differential graded `R`-algebra. Tag 0CS6 asserts a canonical map

`RHom(M, N) ⟶ RHom_O(M ⊗_E^𝐋 K^•, N ⊗_E^𝐋 K^•)`

in `D(R)`. This file constructs that map in `D(R)`, both with the ordinary tensor products and
with the derived ones, and proves that each forgets to the corresponding `D(ℤ)`-valued map.

## Main definitions

* `AlgebraicGeometry.RingedSite.tensorWithComplexHomComplexModulesMapOver`: the map of
  `R`-module-valued differential graded Hom complexes induced by the differential graded tensor
  functor of Tag 09LV.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapModulesOver`: the canonical map
  of Tag 0CS6 in `D(R)`, into the global derived hom of the *ordinary* tensor products.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerivedModulesOver`: the same
  map into the global derived hom of the *derived* tensor products, for every `M`, `N` in
  `D(E, d)`.

## Main results

* `AlgebraicGeometry.RingedSite.tensorWithComplexHomComplexModulesMapOver_forget`,
  `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapModulesOver_forget` and
  `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerivedModulesOver_forget`: each of
  the three maps over `R` forgets to the corresponding `D(ℤ)`-valued map.
* `AlgebraicGeometry.RingedSite.globalDerivedHomForgetApp_naturality_left` and
  `AlgebraicGeometry.RingedSite.globalDerivedHomForgetApp_naturality_right`: forgetting the
  scalars of the global derived hom of Tag 0B6E is natural in both variables.

## References

* [Stacks Project, Tag 0CS6](https://stacks.math.columbia.edu/tag/0CS6)
* [Stacks Project, Tag 0B6E](https://stacks.math.columbia.edu/tag/0B6E)
* [Stacks Project, Tag 09LV](https://stacks.math.columbia.edu/tag/09LV)
* [Stacks Project, Tag 09LX](https://stacks.math.columbia.edu/tag/09LX)
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGradedModule AlgebraicGeometry Opposite
open Stacks.Cohomology.SiteModules
open scoped IsMulCommutative

namespace AlgebraicGeometry.RingedSite

universe u o

attribute [local instance] HasDerivedCategory.standard

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})
  (R : Type o) [CommRing R] [Linear R (TensorModO.{u, u, u, u, u} X)]
  [ScalarSections.{u, u, u, u, u, o} X R]
  (K : CochainComplex (ModO.{u, u, u, u} X) ℤ)

/-- Cancelling the two inverse pairs `u ≫ v` and `B ≫ Cm` out of a composite. -/
private theorem bridgeCancel {C : Type*} [Category C] {a b c d e f : C}
    (p : a ⟶ b) (u : b ⟶ c) (v : c ⟶ b) (A : b ⟶ d) (B : d ⟶ e) (Cm : e ⟶ d) (D : d ⟶ f)
    (hu : u ≫ v = 𝟙 b) (hB : B ≫ Cm = 𝟙 d) :
    p ≫ u ≫ v ≫ (A ≫ B) ≫ Cm ≫ D = p ≫ A ≫ D := by
  simp [reassoc_of% hu, reassoc_of% hB]

/-- The isomorphism `AlgebraicGeometry.RingedSite.homComplexModulesOverDerivedForgetIso` is the
comparison `CategoryTheory.Functor.mapDerivedCategoryFactors` of the forgetful functor of
`R`-modules followed by the class of the morphism of complexes identifying the Hom complex over
`R`, with its scalars forgotten, with the Hom complex of abelian groups. -/
theorem homComplexModulesOverDerivedForgetIso_hom
    (F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (homComplexModulesOverDerivedForgetIso X R F G).hom =
      (forgetBaseRing R).mapDerivedCategoryFactors.hom.app
          ((CompDG.{u, u, u, u, u, o} X R).homComplexModules F G) ≫
        DerivedCategory.Q.map
          (((forgetBaseRing R).mapHomologicalComplex (ComplexShape.up ℤ)).map
              (homComplexModulesRestrictIso X R F G).inv ≫
            (homComplexModulesForgetIso F G).hom) := by
  have hu : (forgetBaseRing R).mapDerivedCategory.map
        ((scalarRestriction X R).mapDerivedCategoryFactors.inv.app
          ((compDGGlobalSections.{u, u, u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).homComplexModules F G)) ≫
      (forgetBaseRing R).mapDerivedCategory.map
        ((scalarRestriction X R).mapDerivedCategoryFactors.hom.app
          ((compDGGlobalSections.{u, u, u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).homComplexModules F G)) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id]
  have hB := Iso.inv_hom_id_app
    (forget₂ (ModuleCat.{u} ↥(GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
      AddCommGrpCat.{u}).mapDerivedCategoryFactors
    ((compDGGlobalSections.{u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).homComplexModules F G)
  rw [homComplexModulesOverDerivedForgetIso, homComplexModulesRestrictDerivedIso,
    homComplexModulesDerivedForgetIso]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.mapIso_inv,
    restrictForgetDerivedIso_hom_app_Q, CategoryTheory.Functor.map_comp, Category.assoc]
  refine Eq.trans (bridgeCancel _ _ _ _ _ _ _ hu hB) ?_
  refine Eq.trans (CategoryTheory.Functor.mapDerivedCategoryFactors_hom_naturality_assoc
    (F := forgetBaseRing R) (homComplexModulesRestrictIso X R F G).inv _) ?_
  exact congrArg (fun z => (forgetBaseRing R).mapDerivedCategoryFactors.hom.app
      ((CompDG.{u, u, u, u, u, o} X R).homComplexModules F G) ≫ z)
    (DerivedCategory.Q.map_comp _ _).symm

/-- Rewriting `m ≫ t` as `u ≫ n` and then cancelling `v ≫ u = 𝟙 b` in a composite. -/
private theorem bridgeNatCancel {C : Type*} [Category C] {a b c d e f : C}
    (p : a ⟶ b) (v : b ⟶ c) (u : c ⟶ b) (m : c ⟶ d) (t : d ⟶ e) (n : b ⟶ e) (w : e ⟶ f)
    (hmt : m ≫ t = u ≫ n) (hvu : v ≫ u = 𝟙 b) :
    p ≫ v ≫ m ≫ t ≫ w = p ≫ n ≫ w := by
  rw [reassoc_of% hmt, reassoc_of% hvu]

/-- **The map of `R`-module-valued differential graded Hom complexes induced by tensoring with
`K`.** This is `DGCategory.DGFunctor.homComplexModulesMap` at the differential graded functor of
Tag 09LV, taken over `R`. -/
def tensorWithComplexHomComplexModulesMapOver
    (M N : (DifferentialGradedModule.dgCategory.{_, _, u}
      (Rep.{u, u, u, u, u, o} X R K).algebra).Obj) :
    (DifferentialGradedModule.dgCategory.{_, _, u}
        (Rep.{u, u, u, u, u, o} X R K).algebra).homComplexModules M N ⟶
      (CompDG.{u, u, u, u, u, o} X R).homComplexModules
        ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj M)
        ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj N) :=
  DGCategory.DGFunctor.homComplexModulesMap
    (tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor M N

/-- **Forgetting the `R`-action of the class of the module-valued differential graded Hom
complex gives the class of the Hom complex of abelian groups.** The forgetful functor is exact,
so it commutes with the localization, and `DGCategory.homComplexModulesForget` is the degreewise
identity. -/
def dgHomComplexModulesDerivedForgetIso
    (M N : (DifferentialGradedModule.dgCategory.{_, _, u}
      (Rep.{u, u, u, u, u, o} X R K).algebra).Obj) :
    (forgetBaseRing R).mapDerivedCategory.obj
        (DerivedCategory.Q.obj ((DifferentialGradedModule.dgCategory.{_, _, u}
          (Rep.{u, u, u, u, u, o} X R K).algebra).homComplexModules M N)) ≅
      DerivedCategory.Q.obj ((DifferentialGradedModule.dgCategory.{_, _, u}
        (Rep.{u, u, u, u, u, o} X R K).algebra).homComplex M N) :=
  (forgetBaseRing R).mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso (DGCategory.homComplexModulesForget _ M N)

/-- **The first leg of the canonical map forgets, on complexes.** Forgetting the `R`-action of
the induced map of module-valued Hom complexes, and identifying source and target with the Hom
complexes of abelian groups, returns
`AlgebraicGeometry.RingedSite.tensorWithComplexHomComplexMap`. -/
theorem complexFirstLeg
    (M N : (DifferentialGradedModule.dgCategory.{_, _, u}
      (Rep.{u, u, u, u, u, o} X R K).algebra).Obj) :
    (DGCategory.homComplexModulesForget _ M N).inv ≫
        ((forgetBaseRing R).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (tensorWithComplexHomComplexModulesMapOver X R K M N) ≫
          (((forgetBaseRing R).mapHomologicalComplex (ComplexShape.up ℤ)).map
              (homComplexModulesRestrictIso X R
                ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj M)
                ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj N)).inv ≫
            (homComplexModulesForgetIso _ _).hom) =
      tensorWithComplexHomComplexMap.{u, o} X R K M N := by
  ext n
  rfl

/-- **The first leg of the canonical map over `R` forgets, in the derived category.** The class
of `AlgebraicGeometry.RingedSite.complexFirstLeg`, read through the comparison
`CategoryTheory.Functor.mapDerivedCategoryFactors` of the forgetful functor of `R`-modules on
either side. -/
theorem tensorWithComplexHomComplexModulesMapOver_forget
    (M N : (DifferentialGradedModule.dgCategory.{_, _, u}
      (Rep.{u, u, u, u, u, o} X R K).algebra).Obj) :
    (dgHomComplexModulesDerivedForgetIso X R K M N).inv ≫
        (forgetBaseRing R).mapDerivedCategory.map
            (DerivedCategory.Q.map (tensorWithComplexHomComplexModulesMapOver X R K M N)) ≫
          (homComplexModulesOverDerivedForgetIso X R
            ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj M)
            ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj N)).hom =
      DerivedCategory.Q.map (tensorWithComplexHomComplexMap.{u, o} X R K M N) := by
  rw [homComplexModulesOverDerivedForgetIso_hom, dgHomComplexModulesDerivedForgetIso,
    Iso.trans_inv, Iso.app_inv, CategoryTheory.Functor.mapIso_inv]
  simp only [Category.assoc]
  refine Eq.trans (bridgeNatCancel _ _ _ _ _ _ _
    (CategoryTheory.Functor.mapDerivedCategoryFactors_hom_naturality
      (F := forgetBaseRing R) (tensorWithComplexHomComplexModulesMapOver X R K M N))
    (Iso.inv_hom_id_app (forgetBaseRing R).mapDerivedCategoryFactors
      ((DifferentialGradedModule.dgCategory.{_, _, u}
        (Rep.{u, u, u, u, u, o} X R K).algebra).homComplexModules M N))) ?_
  refine Eq.trans ?_ (congrArg DerivedCategory.Q.map (complexFirstLeg X R K M N))
  rw [DerivedCategory.Q.map_comp, DerivedCategory.Q.map_comp]

/-- Splitting a composite at an inverse pair `i ≫ j = 𝟙 c`. -/
private theorem bridgeSplit {C : Type*} [Category C] {a b c d e f : C}
    (p : a ⟶ b) (m : b ⟶ c) (i : c ⟶ d) (j : d ⟶ c) (q : c ⟶ e) (w : e ⟶ f)
    {s : a ⟶ d} {t : d ⟶ f}
    (h1 : p ≫ m ≫ i = s) (h2 : j ≫ q ≫ w = t) (hij : i ≫ j = 𝟙 c) :
    p ≫ m ≫ q ≫ w = s ≫ t := by
  subst h1 h2
  simp [reassoc_of% hij]

/-- **The canonical map in `D(R)`.** The differential graded functor of Tag 09LV acts on the
`R`-module-valued differential graded Hom complexes, and the Hom complex of two complexes of
`O`-modules over `R` maps canonically to their global derived hom of Tag 0B6E read over `R`
(`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHomModulesOver`); the composite is this
morphism of `D(R)`.

Its source is the differential graded Hom complex of two differential graded modules, and its
target is the global derived hom of the ordinary tensor products. -/
@[stacks 0CS6 "the canonical map out of the differential graded Hom complex, into \
RHom_O(M ⊗_E K, N ⊗_E K), in the source's D(R)"]
def tensorWithComplexDerivedHomMapModulesOver
    (M N : (DifferentialGradedModule.dgCategory.{_, _, u}
      (Rep.{u, u, u, u, u, o} X R K).algebra).Obj) :
    DerivedCategory.Q.obj ((DifferentialGradedModule.dgCategory.{_, _, u}
        (Rep.{u, u, u, u, u, o} X R K).algebra).homComplexModules M N) ⟶
      (scalarRestriction X R).mapDerivedCategory.obj
        (((globalDerivedHomModules X).obj (op (DerivedCategory.Q.obj
              ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj M)))).obj
          (DerivedCategory.Q.obj
            ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj N))) :=
  DerivedCategory.Q.map (tensorWithComplexHomComplexModulesMapOver X R K M N) ≫
    homComplexToGlobalDerivedHomModulesOver X R _ _

/-- **The canonical map in `D(R)` forgets to the canonical map in `D(ℤ)`.** Forgetting the
`R`-action of `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapModulesOver`, and
identifying its source and its target with those of the `D(ℤ)`-valued map, gives
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMap`. -/
theorem tensorWithComplexDerivedHomMapModulesOver_forget
    (M N : (DifferentialGradedModule.dgCategory.{_, _, u}
      (Rep.{u, u, u, u, u, o} X R K).algebra).Obj) :
    (dgHomComplexModulesDerivedForgetIso X R K M N).inv ≫
        (forgetBaseRing R).mapDerivedCategory.map
            (tensorWithComplexDerivedHomMapModulesOver X R K M N) ≫
          (globalDerivedHomForgetAppOver X R
            (DerivedCategory.Q.obj
              ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj M))
            (DerivedCategory.Q.obj
              ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj N))).hom =
      tensorWithComplexDerivedHomMap.{u, o} X R K M N := by
  rw [tensorWithComplexDerivedHomMapModulesOver, CategoryTheory.Functor.map_comp,
    Category.assoc]
  change _ ≫ _ ≫ _ ≫ _ =
    DerivedCategory.Q.map (tensorWithComplexHomComplexMap.{u, o} X R K M N) ≫
      homComplexToGlobalDerivedHom X
        ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj M)
        ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj N)
  exact bridgeSplit _ _ _ _ _ _
    (tensorWithComplexHomComplexModulesMapOver_forget X R K M N)
    (homComplexToGlobalDerivedHomModulesOver_forget X R _ _)
    (Iso.hom_inv_id _)

/-- **Forgetting the scalars of the global derived hom is natural in the covariant variable.** -/
theorem globalDerivedHomForgetApp_naturality_right
    (A : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (h : L ⟶ L') :
    (underlyingDerivedGroup X).map (((globalDerivedHomModules X).obj (op A)).map h) ≫
        (globalDerivedHomForgetApp X A L').hom =
      (globalDerivedHomForgetApp X A L).hom ≫ ((globalDerivedHom X).obj (op A)).map h :=
  (globalDerivedHomForget X A).hom.naturality h

/-- **Forgetting the scalars of the global derived hom is natural in the contravariant
variable.** -/
theorem globalDerivedHomForgetApp_naturality_left
    {A A' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (g : A' ⟶ A)
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (underlyingDerivedGroup X).map (((globalDerivedHomModules X).map (op g)).app L) ≫
        (globalDerivedHomForgetApp X A' L).hom =
      (globalDerivedHomForgetApp X A L).hom ≫ ((globalDerivedHom X).map (op g)).app L :=
  derivedGlobalSectionsModulesForget_naturality X
    (((derivedSheafHomBifunctor X).map (op g)).app L)

/-- Naturality of a transformation `α` composed with a square commuting after applying `G`. -/
private theorem natTrans_comp_naturality {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    {α : F ⟶ G} {X Y : C} {f : X ⟶ Y} {Z W : D} {b : G.obj X ⟶ Z} {b' : G.obj Y ⟶ W}
    {t : Z ⟶ W} (h : G.map f ≫ b' = b ≫ t) :
    F.map f ≫ α.app Y ≫ b' = (α.app X ≫ b) ≫ t := by
  rw [α.naturality_assoc, h, Category.assoc]

/-- **Forgetting the `R`-action of the global derived hom is natural in the covariant
variable.** -/
theorem globalDerivedHomForgetAppOver_naturality_right
    (A : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (h : L ⟶ L') :
    ((scalarRestriction X R).mapDerivedCategory ⋙ (forgetBaseRing R).mapDerivedCategory).map
          (((globalDerivedHomModules X).obj (op A)).map h) ≫
        (globalDerivedHomForgetAppOver X R A L').hom =
      (globalDerivedHomForgetAppOver X R A L).hom ≫ ((globalDerivedHom X).obj (op A)).map h := by
  exact natTrans_comp_naturality (globalDerivedHomForgetApp_naturality_right ..)

/-- **Forgetting the `R`-action of the global derived hom is natural in the contravariant
variable.** -/
theorem globalDerivedHomForgetAppOver_naturality_left
    {A A' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (g : A' ⟶ A)
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((scalarRestriction X R).mapDerivedCategory ⋙ (forgetBaseRing R).mapDerivedCategory).map
          (((globalDerivedHomModules X).map (op g)).app L) ≫
        (globalDerivedHomForgetAppOver X R A' L).hom =
      (globalDerivedHomForgetAppOver X R A L).hom ≫ ((globalDerivedHom X).map (op g)).app L := by
  exact natTrans_comp_naturality (globalDerivedHomForgetApp_naturality_left ..)

/-- Rewriting a composite along the two commuting squares `h₂` and `h₁`. -/
private theorem bridgeChain {C : Type*} [Category C] {a b c d e f g h : C}
    (p : a ⟶ b) (m : b ⟶ c) (t₁ : c ⟶ d) (t₂ : d ⟶ e) (x : e ⟶ f)
    (x₂ : d ⟶ g) (u₂ : g ⟶ f) (x₁ : c ⟶ h) (u₁ : h ⟶ g)
    (h₂ : t₂ ≫ x = x₂ ≫ u₂) (h₁ : t₁ ≫ x₂ = x₁ ≫ u₁) :
    p ≫ m ≫ t₁ ≫ t₂ ≫ x = (p ≫ m ≫ x₁) ≫ u₁ ≫ u₂ := by
  simp only [h₂, reassoc_of% h₁, Category.assoc]

/-- **The canonical map `RHom(M, N) ⟶ RHom_O(M ⊗_E^𝐋 K^•, N ⊗_E^𝐋 K^•)` in `D(R)`**, *for every*
`M`, `N` *in* `D(E, d)`. The canonical map of
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapModulesOver`, taken at the chosen
property-(P) representatives of `M` and `N`, is read into the global derived hom of the *derived*
tensor products,

`RHom(M, N) ⟶ RHom_O(M ⊗_E^𝐋 K^•, N ⊗_E^𝐋 K^•)`,

by transporting both arguments along
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedRepIso`: in the contravariant argument the
isomorphism is used as it stands, and in the covariant one it is inverted.

There is no hypothesis on `M` or `N`. -/
@[stacks 0CS6 "the canonical map RHom(M, N) ⟶ RHom_O(M ⊗_E^𝐋 K, N ⊗_E^𝐋 K) in the source's \
D(R), for every M, N in D(E, d)"]
def tensorWithComplexDerivedHomMapDerivedModulesOver
    (M N : DifferentialGradedModule.derivedCategory (Rep.{u, u, u, u, u, o} X R K).algebra) :
    DerivedCategory.Q.obj
        ((DifferentialGradedModule.dgCategory.{_, _, u}
            (Rep.{u, u, u, u, u, o} X R K).algebra).homComplexModules
          (DifferentialGradedModule.propertyPModel.{o, u, 0}
            (Rep.{u, u, u, u, u, o} X R K).algebra M)
          (DifferentialGradedModule.propertyPModel.{o, u, 0}
            (Rep.{u, u, u, u, u, o} X R K).algebra N)) ⟶
      (scalarRestriction X R).mapDerivedCategory.obj
        (((globalDerivedHomModules X).obj
            (op ((tensorWithComplexDerived.{u, u, u, u, u, o} X R K).obj M))).obj
          ((tensorWithComplexDerived.{u, u, u, u, u, o} X R K).obj N)) :=
  tensorWithComplexDerivedHomMapModulesOver X R K _ _ ≫
    (scalarRestriction X R).mapDerivedCategory.map
      (((globalDerivedHomModules X).map
          (op (tensorWithComplexDerivedRepIso.{u, o} X R K M).hom)).app _ ≫
        ((globalDerivedHomModules X).obj _).map
          (tensorWithComplexDerivedRepIso.{u, o} X R K N).inv)

/-- **The canonical map in `D(R)` into the derived tensor products forgets to the one in
`D(ℤ)`.** Forgetting the `R`-action of
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerivedModulesOver`, and identifying
its source and its target with those of the `D(ℤ)`-valued map, gives
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerived`. -/
theorem tensorWithComplexDerivedHomMapDerivedModulesOver_forget
    (M N : DifferentialGradedModule.derivedCategory (Rep.{u, u, u, u, u, o} X R K).algebra) :
    (dgHomComplexModulesDerivedForgetIso X R K _ _).inv ≫
        (forgetBaseRing R).mapDerivedCategory.map
            (tensorWithComplexDerivedHomMapDerivedModulesOver X R K M N) ≫
          (globalDerivedHomForgetAppOver X R
            ((tensorWithComplexDerived.{u, u, u, u, u, o} X R K).obj M)
            ((tensorWithComplexDerived.{u, u, u, u, u, o} X R K).obj N)).hom =
      tensorWithComplexDerivedHomMapDerived.{u, o} X R K M N := by
  rw [tensorWithComplexDerivedHomMapDerivedModulesOver]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  refine Eq.trans (bridgeChain _ _ _ _ _ _ _ _ _
    (globalDerivedHomForgetAppOver_naturality_right X R
      ((tensorWithComplexDerived.{u, u, u, u, u, o} X R K).obj M)
      (tensorWithComplexDerivedRepIso.{u, o} X R K N).inv)
    (globalDerivedHomForgetAppOver_naturality_left X R
      (tensorWithComplexDerivedRepIso.{u, o} X R K M).hom
      (DerivedCategory.Q.obj ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
        (DifferentialGradedModule.propertyPModel.{o, u, 0}
          (Rep.{u, u, u, u, u, o} X R K).algebra N))))) ?_
  rw [tensorWithComplexDerivedHomMapModulesOver_forget]
  rfl

end AlgebraicGeometry.RingedSite

end
