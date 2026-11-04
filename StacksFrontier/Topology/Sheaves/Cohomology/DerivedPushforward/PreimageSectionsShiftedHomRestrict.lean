module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.HomPresheafValueRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PreimageCohomologyEvaluationRestrict

/-!
# `Ext` over an inverse image in degree zero is compatible with restriction

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `K`, `L` be objects of the
unbounded derived category `D(𝒪_X)`. For an open `V ⊆ Y` the degree-`i` hypercohomology
`H^i(f⁻¹ V, RSheafHom(K, L))` is identified with the group `Ext^i(K|_{f⁻¹ V}, L|_{f⁻¹ V})` of
degree-`i` morphisms of the restrictions by
`Stacks.Cohomology.UnboundedHigherDirectImage.preimageSectionsHomologyEquivShiftedHom`. This file
proves that in degree zero this identification is compatible with restriction: for `V' ≤ V` the
restriction map on the hypercohomology of derived sections over the inverse images,
`Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSectionsRestrictHomology`, is carried to
the restriction `AlgebraicGeometry.RingedSite.restrictDerivedHom` of a morphism of derived
categories along `f⁻¹ V' ⟶ f⁻¹ V`.

## Main definitions

* `Stacks.Cohomology.UnboundedHigherDirectImage.preimageSectionsHomologyIso`: the degree-`i`
  hypercohomology of `RSheafHom(K, L)` over `f⁻¹ V`, read as an abelian group, is the degree-`i`
  homology of the complex of sections of `RSheafHom(K, L)` over `f⁻¹ V`.

## Main results

In the namespace `Stacks.Cohomology.UnboundedHigherDirectImage`:

* `preimageSectionsHomologyEquivShiftedHom_zero_restrict`: for `V' ≤ V`, restricting a class in
  `H^0(f⁻¹ V, RSheafHom(K, L))` to `f⁻¹ V'` and identifying it with a morphism of derived
  categories agrees with identifying it over `f⁻¹ V` and restricting the morphism.
* `preimageSectionsHomologyIso_restrict` and `preimageSectionsHomologyIso_hom_restrict`: the
  restriction square for `preimageSectionsHomologyIso`, on elements and as an equality of
  morphisms of abelian groups, with the restriction map
  `AlgebraicGeometry.RingedSite.sectionComplexRestrict` on the homology of the complexes of
  sections.

In the namespace `Stacks.DerivedCategoryComparisons`, for exact functors `T` and `G` between
abelian categories:

* `derivedHomologyIso_square_of_representatives`: a square on degree-`i` homology induced by a
  morphism `δ` of derived categories and a map `r : M ⟶ T(N)` of complexes representing it.
* `derivedHomologyIso_forget_square_of_representatives`: the same square after applying `G`, with
  the comparisons of `G` and `T ⋙ G` with homology.
* `exactHomologyIso_homologyMap_square` and `exactHomologyIso_inv_homologyMap_square`: the
  commutation of `G` with homology moved past `H^i(r)`, in both directions.
* `derivedHomologyIso_hom_app_Q_conj`: the commutation of an exact functor with homology on the
  derived category, conjugated by the factorizations of the homology functors through complexes,
  is the commutation on complexes.

## References

* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsLeray (derivedPreimageSections preimageSections
  derivedPreimageSectionsRestrictHomology derivedPreimageSectionsRestrict
  preimageSectionsRestrict)
open Stacks.SheafOfModules (homSheafComplex homSheafObject ringedSite
  homSheafComplexSectionHomologyEquiv homologyMapHomologicalComplexIso)

namespace Stacks.DerivedCategoryComparisons

universe v₁ v₂ v₃ u₁ u₂ u₃

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

section Bookkeeping

variable {Z : Type u₁} [Category.{v₁} Z]

/-- A composite whose outer two legs are cancelled by the legs flanking it. -/
private theorem cancelOuter {w x y z z' : Z} (a : w ⟶ x) (b : x ⟶ w) (c : w ⟶ y) (d : y ⟶ z)
    (e : z ⟶ z') (h : z' ⟶ z) (hab : a ≫ b = 𝟙 w) (heh : e ≫ h = 𝟙 z) :
    a ≫ (b ≫ c ≫ d ≫ e) ≫ h = c ≫ d := by
  simp only [Category.assoc]
  rw [← Category.assoc a b, hab, Category.id_comp, heh, Category.comp_id]

/-- A commuting square, read with its two vertical isomorphisms inverted. -/
private theorem invSquare {w x y z : Z} (μ : w ≅ x) (ν : z ≅ y) (a : x ⟶ y) (b : w ⟶ z)
    (h : μ.hom ≫ a = b ≫ ν.hom) : a ≫ ν.inv = μ.inv ≫ b := by
  rw [Iso.eq_inv_comp, reassoc_of% h, Iso.hom_inv_id, Category.comp_id]

/-- Re-bracketing a composite of four morphisms. -/
private theorem assoc₃ {w x y z z' : Z} (a : w ⟶ x) (b : x ⟶ y) (c : y ⟶ z) (d : z ⟶ z') :
    a ≫ b ≫ c ≫ d = (a ≫ b ≫ c) ≫ d := by
  simp only [Category.assoc]

end Bookkeeping

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] (T : A ⥤ B) [T.Additive]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T] (i : ℤ)

/-- **The homology comparison of an exact functor, conjugated back onto complexes.**  For an
exact additive functor `T`, the comparison `H^i(T(-)) ≅ T(H^i(-))` on the derived category, read
at the class of a complex `N` and conjugated by the factorizations of the two homology functors
through the category of complexes, is the comparison `H^i(T(N)) ≅ T(H^i(N))` on complexes. -/
theorem derivedHomologyIso_hom_app_Q_conj (N : CochainComplex A ℤ) :
    (DerivedCategory.homologyFunctor B i).map (T.mapDerivedCategoryFactors.inv.app N) ≫
        (Stacks.Homology.derivedHomologyIso T i).hom.app (DerivedCategory.Q.obj N) ≫
          T.map ((DerivedCategory.homologyFunctorFactors A i).hom.app N) =
      (DerivedCategory.homologyFunctorFactors B i).hom.app
          ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) ≫
        (Stacks.Homology.exactHomologyIso T i).hom.app N := by
  rw [Stacks.Cohomology.HypercohomologyEdge.derivedHomologyIso_hom_app_Q]
  exact cancelOuter _ _ _ _ _ _
    (by simp) (by simp)

/-- **A square on degree-`i` homology, from one on the derived category.**  Let `M` and `N` be
complexes whose classes `κ`, `κ'` identify with objects `Zb`, `Za` of the two derived categories,
let `δ : Zb ⟶ T(Za)` be a morphism, and let `r : M ⟶ T(N)` be a map of complexes inducing `δ`
through those identifications.  Then on degree-`i` homology, `δ` followed by `T` applied to the
identification of `H^i(Za)` with `H^i(N)` is the identification of `H^i(Zb)` with `H^i(M)`
followed by `H^i(r)` and the comparison of `H^i(T(N))` with `T(H^i(N))`. -/
theorem derivedHomologyIso_square_of_representatives {M : CochainComplex B ℤ}
    {N : CochainComplex A ℤ} {Zb : DerivedCategory B} {Za : DerivedCategory A}
    (κ : DerivedCategory.Q.obj M ≅ Zb) (κ' : DerivedCategory.Q.obj N ≅ Za)
    (δ : Zb ⟶ T.mapDerivedCategory.obj Za)
    (r : M ⟶ (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
    (hr : κ.hom ≫ δ = DerivedCategory.Q.map r ≫
      T.mapDerivedCategoryFactors.inv.app N ≫ T.mapDerivedCategory.map κ'.hom) :
    (DerivedCategory.homologyFunctor B i).map δ ≫
        (Stacks.Homology.derivedHomologyIso T i).hom.app Za ≫
          T.map ((DerivedCategory.homologyFunctor A i).map κ'.inv ≫
            (DerivedCategory.homologyFunctorFactors A i).hom.app N) =
      ((DerivedCategory.homologyFunctor B i).map κ.inv ≫
          (DerivedCategory.homologyFunctorFactors B i).hom.app M) ≫
        HomologicalComplex.homologyMap r i ≫
          (Stacks.Homology.exactHomologyIso T i).hom.app N := by
  have hδ : δ ≫ T.mapDerivedCategory.map κ'.inv =
      κ.inv ≫ DerivedCategory.Q.map r ≫ T.mapDerivedCategoryFactors.inv.app N := by
    rw [Iso.eq_inv_comp, reassoc_of% hr, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  have hnat : (Stacks.Homology.derivedHomologyIso T i).hom.app Za ≫
        T.map ((DerivedCategory.homologyFunctor A i).map κ'.inv) =
      (DerivedCategory.homologyFunctor B i).map (T.mapDerivedCategory.map κ'.inv) ≫
        (Stacks.Homology.derivedHomologyIso T i).hom.app (DerivedCategory.Q.obj N) :=
    ((Stacks.Homology.derivedHomologyIso T i).hom.naturality κ'.inv).symm
  have hfac := (DerivedCategory.homologyFunctorFactors B i).hom.naturality r
  simp only [CategoryTheory.Functor.comp_map] at hfac
  rw [CategoryTheory.Functor.map_comp,
    ← Category.assoc ((Stacks.Homology.derivedHomologyIso T i).hom.app Za), hnat]
  simp only [Category.assoc]
  rw [← Category.assoc ((DerivedCategory.homologyFunctor B i).map δ),
    ← CategoryTheory.Functor.map_comp, hδ, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [derivedHomologyIso_hom_app_Q_conj,
    ← Category.assoc ((DerivedCategory.homologyFunctor B i).map (DerivedCategory.Q.map r)), hfac]
  simp only [Category.assoc]
  rfl

variable {C : Type u₃} [Category.{v₃} C] [Abelian C] (G : B ⥤ C) [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

omit [HasDerivedCategory A] [HasDerivedCategory B] in
/-- **The homology comparison of a second exact functor, moved past the first.**  For `r : M ⟶
T(N)` a map of complexes and `G` a second exact functor, the identification of `H^i(G(M))` with
`G(H^i(M))` followed by `G` applied to `H^i(r)` and to the comparison for `T` is `H^i(G(r))`
followed by the comparison for the composite `T ⋙ G`. -/
theorem exactHomologyIso_homologyMap_square {M : CochainComplex B ℤ} {N : CochainComplex A ℤ}
    (r : M ⟶ (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) :
    (Stacks.Homology.exactHomologyIso G i).hom.app M ≫
        G.map (HomologicalComplex.homologyMap r i) ≫
          G.map ((Stacks.Homology.exactHomologyIso T i).hom.app N) =
      HomologicalComplex.homologyMap
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map r) i ≫
        (Stacks.Homology.exactHomologyIso (T ⋙ G) i).hom.app N := by
  have hnat := (Stacks.Homology.exactHomologyIso G i).hom.naturality r
  simp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.comp_obj,
    HomologicalComplex.homologyFunctor_map] at hnat
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg
    (fun t => t ≫ G.map ((Stacks.Homology.exactHomologyIso T i).hom.app N)) hnat.symm) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact congrArg (fun t => HomologicalComplex.homologyMap
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map r) i ≫ t)
    (Stacks.Homology.exactHomologyIso_comp_hom_app T G i N)

omit [HasDerivedCategory A] [HasDerivedCategory B] in
/-- **The same square, read with the two comparisons of homology inverted.** `G` applied to
`H^i(r)` and the comparison for `T`, followed by the inverse comparison for `T ⋙ G`, is the
inverse comparison for `G` followed by `H^i(G(r))`. -/
theorem exactHomologyIso_inv_homologyMap_square {M : CochainComplex B ℤ}
    {N : CochainComplex A ℤ}
    (r : M ⟶ (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) :
    G.map (HomologicalComplex.homologyMap r i ≫
          (Stacks.Homology.exactHomologyIso T i).hom.app N) ≫
        (Stacks.Homology.exactHomologyIso (T ⋙ G) i).inv.app N =
      (Stacks.Homology.exactHomologyIso G i).inv.app M ≫
        HomologicalComplex.homologyMap
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map r) i :=
  invSquare ((Stacks.Homology.exactHomologyIso G i).app M)
    ((Stacks.Homology.exactHomologyIso (T ⋙ G) i).app N) _ _
    ((congrArg (fun t => (Stacks.Homology.exactHomologyIso G i).hom.app M ≫ t)
        (CategoryTheory.Functor.map_comp G (HomologicalComplex.homologyMap r i)
          ((Stacks.Homology.exactHomologyIso T i).hom.app N))).trans
      (exactHomologyIso_homologyMap_square T i G r))

/-- **A square on degree-`i` homology after two exact functors, from one on the derived
category.** With `κ`, `κ'`, `δ` and `r` as in `derivedHomologyIso_square_of_representatives` and
`G` a second exact functor, `G` applied to the left side of that square, followed by the inverse
comparison `(T ⋙ G)(H^i(N)) ≅ H^i((T ⋙ G)(N))`, is `G` applied to the identification of
`H^i(Zb)` with `H^i(M)`, followed by the inverse comparison for `G` and `H^i(G(r))`. -/
theorem derivedHomologyIso_forget_square_of_representatives {M : CochainComplex B ℤ}
    {N : CochainComplex A ℤ} {Zb : DerivedCategory B} {Za : DerivedCategory A}
    (κ : DerivedCategory.Q.obj M ≅ Zb) (κ' : DerivedCategory.Q.obj N ≅ Za)
    (δ : Zb ⟶ T.mapDerivedCategory.obj Za)
    (r : M ⟶ (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
    (hr : κ.hom ≫ δ = DerivedCategory.Q.map r ≫
      T.mapDerivedCategoryFactors.inv.app N ≫ T.mapDerivedCategory.map κ'.hom) :
    G.map ((DerivedCategory.homologyFunctor B i).map δ ≫
          (Stacks.Homology.derivedHomologyIso T i).hom.app Za) ≫
        ((T ⋙ G).map ((DerivedCategory.homologyFunctor A i).map κ'.inv ≫
              (DerivedCategory.homologyFunctorFactors A i).hom.app N) ≫
            (Stacks.Homology.exactHomologyIso (T ⋙ G) i).inv.app N) =
      (G.map ((DerivedCategory.homologyFunctor B i).map κ.inv ≫
            (DerivedCategory.homologyFunctorFactors B i).hom.app M) ≫
          (Stacks.Homology.exactHomologyIso G i).inv.app M) ≫
        HomologicalComplex.homologyMap
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map r) i := by
  have hGA := congrArg (fun t => G.map t)
    (derivedHomologyIso_square_of_representatives T i κ κ' δ r hr)
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at hGA
  simp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% hGA]
  refine Eq.trans (congrArg (fun t =>
      G.map ((DerivedCategory.homologyFunctor B i).map κ.inv) ≫
        G.map ((DerivedCategory.homologyFunctorFactors B i).hom.app M) ≫ t)
    (exactHomologyIso_inv_homologyMap_square T i G r)) ?_
  exact assoc₃ _ _ _ _

end Stacks.DerivedCategoryComparisons

namespace Stacks.Cohomology.UnboundedHigherDirectImage

universe u

attribute [local instance] HasDerivedCategory.standard
  Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteLimits
  Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteColimits
attribute [local instance] isGrothendieckAbelian_moduleSheaves

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

variable (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))

/-- **The hypercohomology over an inverse image is the homology of the complex of sections.**
The degree-`i` hypercohomology `H^i(f⁻¹ V, RSheafHom(K, L))`, read as an abelian group, is the
degree-`i` homology of the complex of sections of `RSheafHom(K, L)` over `f⁻¹ V`. -/
def preimageSectionsHomologyIso (V : Opens Y.carrier) (i : ℤ) :
    (forget₂ (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) AddCommGrpCat.{u}).obj
        ((DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) i).obj
          ((derivedPreimageSections f V).obj (homSheafObject X.sheaf K L))) ≅
      (Stacks.SheafOfModules.sectionComplex X.sheaf (homSheafComplex X.sheaf K L)
        ((opensMap f).obj V)).homology i :=
  (forget₂ (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) AddCommGrpCat.{u}).mapIso
      ((DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) i).mapIso
          (preimageSectionsKInjectiveIso f V (homSheafComplex X.sheaf K L)
            (Stacks.SheafOfModules.isKInjective_homSheafComplex X.sheaf K L)).symm ≪≫
        (DerivedCategory.homologyFunctorFactors
            (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) i).app
          (((preimageSections f V).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (homSheafComplex X.sheaf K L))) ≪≫
    (homologyMapHomologicalComplexIso
      (forget₂ (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) AddCommGrpCat.{u})
      (((preimageSections f V).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (homSheafComplex X.sheaf K L)) i).symm

/-- **The `Ext` identification over an inverse image, written out.**  It is
`preimageSectionsHomologyIso` followed by the degree-`i` identification of [Stacks, Tag 08DK] on
the open `f⁻¹ V`. -/
theorem preimageSectionsHomologyEquivShiftedHom_apply (V : Opens Y.carrier) (i : ℤ)
    (s : ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) i).obj
      ((derivedPreimageSections f V).obj (homSheafObject X.sheaf K L)) : Type u)) :
    preimageSectionsHomologyEquivShiftedHom f K L V i s =
      homSheafComplexSectionHomologyEquiv X.sheaf K L ((opensMap f).obj V) i
        ((preimageSectionsHomologyIso f K L V i).addCommGroupIsoToAddEquiv s) :=
  rfl

/-- **The restriction square for `preimageSectionsHomologyIso`.**  For `V' ≤ V`, the restriction
map on the hypercohomology of derived sections over the inverse images is carried by
`preimageSectionsHomologyIso` to the map induced on homology by the restriction of the complexes
of sections from `f⁻¹ V` to `f⁻¹ V'`. -/
theorem preimageSectionsHomologyIso_hom_restrict {V V' : Opens Y.carrier} (hV : V' ≤ V)
    (i : ℤ) :
    (forget₂ (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) AddCommGrpCat.{u}).map
          ((derivedPreimageSectionsRestrictHomology f hV i).app
            (homSheafObject X.sheaf K L)) ≫
        (preimageSectionsHomologyIso f K L V' i).hom =
      (preimageSectionsHomologyIso f K L V i).hom ≫
        HomologicalComplex.homologyMap
          (AlgebraicGeometry.RingedSite.sectionComplexRestrict (ringedSite X.sheaf)
            (homSheafComplex X.sheaf K L) ((opensMap f).map hV.hom)) i :=
  Stacks.DerivedCategoryComparisons.derivedHomologyIso_forget_square_of_representatives
    (ModuleCat.restrictScalars ((structureSheafRing Y).obj.map hV.hom.op).hom) i
    (forget₂ (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) AddCommGrpCat.{u})
    (preimageSectionsKInjectiveIso f V (homSheafComplex X.sheaf K L)
      (Stacks.SheafOfModules.isKInjective_homSheafComplex X.sheaf K L))
    (preimageSectionsKInjectiveIso f V' (homSheafComplex X.sheaf K L)
      (Stacks.SheafOfModules.isKInjective_homSheafComplex X.sheaf K L))
    ((derivedPreimageSectionsRestrict f hV).app (homSheafObject X.sheaf K L))
    ((NatTrans.mapHomologicalComplex (preimageSectionsRestrict f hV)
      (ComplexShape.up ℤ)).app (homSheafComplex X.sheaf K L))
    (Stacks.Cohomology.DerivedSectionsLeray.preimageSectionsKInjectiveIso_restrict f hV
      (homSheafComplex X.sheaf K L)
      (Stacks.SheafOfModules.isKInjective_homSheafComplex X.sheaf K L))

/-- **The restriction square for `preimageSectionsHomologyIso`, on an element.** -/
theorem preimageSectionsHomologyIso_restrict {V V' : Opens Y.carrier} (hV : V' ≤ V) (i : ℤ)
    (s : ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) i).obj
      ((derivedPreimageSections f V).obj (homSheafObject X.sheaf K L)) : Type u)) :
    (preimageSectionsHomologyIso f K L V' i).addCommGroupIsoToAddEquiv
        ((derivedPreimageSectionsRestrictHomology f hV i).app
          (homSheafObject X.sheaf K L) s) =
      HomologicalComplex.homologyMap
        (AlgebraicGeometry.RingedSite.sectionComplexRestrict (ringedSite X.sheaf)
          (homSheafComplex X.sheaf K L) ((opensMap f).map hV.hom)) i
        ((preimageSectionsHomologyIso f K L V i).addCommGroupIsoToAddEquiv s) := by
  have h := congrArg ConcreteCategory.hom
    (preimageSectionsHomologyIso_hom_restrict f K L hV i)
  exact DFunLike.congr_fun h s

/-- **Restriction in the open of the `Ext` identification over an inverse image, in degree
zero.**  For `V' ≤ V`, restricting a class in `H^0(f⁻¹ V, RSheafHom(K, L))` to `f⁻¹ V'` and then
identifying it with a morphism `K|_{f⁻¹ V'} ⟶ L|_{f⁻¹ V'}` gives the same morphism as identifying
it over `f⁻¹ V` and restricting the resulting morphism of derived categories along
`f⁻¹ V' ⟶ f⁻¹ V`.  The degree-zero shift of the target is normalised away on both sides. -/
theorem preimageSectionsHomologyEquivShiftedHom_zero_restrict {V V' : Opens Y.carrier}
    (hV : V' ≤ V)
    (s : ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) 0).obj
      ((derivedPreimageSections f V).obj (homSheafObject X.sheaf K L)) : Type u)) :
    AlgebraicGeometry.RingedSite.restrictDerivedHom (ringedSite X.sheaf)
        ((opensMap f).map hV.hom) K L
        (Linear.homCongr ℤ (Iso.refl _)
          ((shiftFunctorZero _ ℤ).app ((preimageRestrict f V).obj L))
          (preimageSectionsHomologyEquivShiftedHom f K L V 0 s)) =
      Linear.homCongr ℤ (Iso.refl _)
        ((shiftFunctorZero _ ℤ).app ((preimageRestrict f V').obj L))
        (preimageSectionsHomologyEquivShiftedHom f K L V' 0
          ((derivedPreimageSectionsRestrictHomology f hV 0).app
            (homSheafObject X.sheaf K L) s)) := by
  have h := Stacks.SheafOfModules.homSheafComplexSectionHomologyEquiv_zero_restrict
    X.sheaf K L ((opensMap f).map hV.hom)
    ((preimageSectionsHomologyIso f K L V 0).addCommGroupIsoToAddEquiv s)
  exact ((congrArg (fun t => Linear.homCongr ℤ (Iso.refl _)
    ((shiftFunctorZero _ ℤ).app ((preimageRestrict f V').obj L))
    (homSheafComplexSectionHomologyEquiv X.sheaf K L ((opensMap f).obj V') 0 t))
    (preimageSectionsHomologyIso_restrict f K L hV 0 s)).trans h).symm

end Stacks.Cohomology.UnboundedHigherDirectImage

end
