module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomShiftSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomDegreeNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomRepresentativePair

/-!
# The degree-`n` reading of the canonical map

Let `(C, O)` be a ringed site, let `F` be a K-flat complex of `O`-modules and let `G` be a
K-injective one. The canonical map `Hom^•(F, G) ⟶ RHom_O(F, G)` of
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom` is read on degree-`n` cohomology
here: through the degree-`n` identification
`AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv` of Tag 0B6E on the target and Tag 0A8Z
on the source it is the localization functor `K(O) ⥤ D(O)` on morphism groups.

This is the degree-`n` form of
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_homology_zero_of_isKFlat`, obtained
from it by reading the square
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_shift` on degree-zero homology: for a
K-flat `F` and a K-injective `G` the pair `(F, G[n])` is a representative pair along with
`(F, G)`, because `G[n]` is K-injective and Tag 0A96 restores the K-injectivity of the internal
Hom complex.

## Main definitions

* `AlgebraicGeometry.RingedSite.globalDerivedHomTargetShiftIsoOfKInjective`: the commutation of
  the *global* derived hom with the translation in its covariant variable, at a K-injective
  target.

## Main results

* `AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_shift_iso`: the square
  `AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_shift`, restated with
  `AlgebraicGeometry.RingedSite.globalDerivedHomTargetShiftIsoOfKInjective`.
* `AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_shift_comp`: the two isomorphisms
  the degree-`n` identification of the global derived hom is built from, composed with the
  `n`-shift of the canonical map, give the canonical map at `(F, G[n])`.
* `AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv_homologyMap_eq_degreeZero`: the
  degree-`n` reading reduced to the degree-zero one at the pair `(F, G[n])`.
* `AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_homology_of_isKFlat`: **the
  degree-`n` reading.** For a K-flat `F` and a K-injective `G` the degree-`n` cohomology of the
  canonical map is the localization functor on morphism groups.

## Implementation notes

*Why the identification is stated against the inverse of the commutation of the localization
functor with the translation.* `AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv` at
`(Q F, Q G)` lands in `Hom_{D(O)}(Q F, (Q G)[n])`, whereas Tag 0A8Z in degree `n` produces a
morphism into the homotopy class of `G[n]`, hence into `Q (G[n])` after localization. The two
differ by `(DerivedCategory.Q.commShiftIso n).app G`, which is therefore carried explicitly in
the statements rather than absorbed: absorbing it would make the identification read as if the
localization functor commuted with the translation on the nose.

*Associativity.* The target of `AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom` is
spelled with `AlgebraicGeometry.RingedSite.globalDerivedHom` while the morphisms it is composed
with are spelled with `AlgebraicGeometry.RingedSite.derivedModuleGlobalSections` applied to the
derived internal Hom. The two are equal by `rfl`
(`AlgebraicGeometry.RingedSite.globalDerivedHom_obj_obj`) but not syntactically, and
`CategoryTheory.Category.assoc` does not instantiate across the mismatch — so a composite
containing the canonical map stays unassociated and `rw`, `simp` and `reassoc_of%` all fail on it.
`AlgebraicGeometry.RingedSite.comp_inv_eq_of_comp_hom_eq` generalises the morphisms to variables of
a plain category, so that associativity applies inside the lemma and the application only has to
typecheck; the remaining proofs are chained out of `congrArg` and `Eq.trans`, which likewise only
require the terms to typecheck.

## References

* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
* [Stacks Project, Tag 0B6E](https://stacks.math.columbia.edu/tag/0B6E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections CochainComplex.HomComplex

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})

/-- **The global derived hom commutes with the translation in its covariant variable, at a
K-injective target**: `RHom_O(Q F, Q (G[n])) ≅ RHom_O(Q F, Q G)[n]`.

This is the commutation `AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIsoOfKInjective`
of the derived internal Hom followed by the commutation of derived global sections with the
translation. -/
noncomputable def globalDerivedHomTargetShiftIsoOfKInjective
    (F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [G.IsKInjective] (n : ℤ) :
    (derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj F))).obj
          (DerivedCategory.Q.obj (G⟦n⟧))) ≅
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj F))).obj
          (DerivedCategory.Q.obj G)))⟦n⟧ :=
  (derivedModuleGlobalSections X).mapIso
      (derivedSheafHomTargetShiftIsoOfKInjective X F G n) ≪≫
    ((derivedModuleGlobalSections X).commShiftIso n).app
      (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj F))).obj
        (DerivedCategory.Q.obj G))

/-- **The square of
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_shift`, restated** with the two
commutations with the translation bundled into
`AlgebraicGeometry.RingedSite.globalDerivedHomTargetShiftIsoOfKInjective`, and with the target of
the canonical map written as derived global sections of the derived internal Hom. -/
theorem homComplexToGlobalDerivedHom_shift_iso (F G : CochainComplex (SheafOfModules.{u}
  (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) [G.IsKInjective]
    (n : ℤ) :
    DerivedCategory.Q.map (homComplexTargetShiftIso F G n).hom ≫
        (homComplexToGlobalDerivedHom X F (G⟦n⟧) :
            DerivedCategory.Q.obj (F.HomComplex (G⟦n⟧)) ⟶
              (derivedModuleGlobalSections X).obj
                (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj F))).obj
                  (DerivedCategory.Q.obj (G⟦n⟧)))) ≫
          (globalDerivedHomTargetShiftIsoOfKInjective X F G n).hom =
      (DerivedCategory.Q.commShiftIso n).hom.app (F.HomComplex G) ≫
        ((CategoryTheory.shiftFunctor (DerivedCategory AddCommGrpCat.{u}) n).map
            (homComplexToGlobalDerivedHom X F G) :
          (DerivedCategory.Q.obj (F.HomComplex G))⟦n⟧ ⟶
            ((derivedModuleGlobalSections X).obj
              (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj F))).obj
                (DerivedCategory.Q.obj G)))⟦n⟧) :=
  homComplexToGlobalDerivedHom_shift X F G n

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- Cancelling an isomorphism on the right of a composite: if `b₁ ≫ b₂ ≫ e.hom = α.hom ≫ p`
then `p ≫ e.inv = α.inv ≫ b₁ ≫ b₂`. -/
private lemma comp_inv_eq_of_comp_hom_eq {C : Type*} [Category C] {W W' Z V V' : C} (α : W ≅ W')
  (p : W' ⟶ Z)
    (b₁ : W ⟶ V') (b₂ : V' ⟶ V) (e : V ≅ Z) (h : b₁ ≫ b₂ ≫ e.hom = α.hom ≫ p) :
    p ≫ e.inv = α.inv ≫ b₁ ≫ b₂ := by
  simp [Iso.comp_inv_eq, h]

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive] in
/-- The `n`-shift of the canonical map,
followed by the two isomorphisms out of which
`AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv` is built and by the transport of the
covariant variable from `(Q G)[n]` to `Q (G[n])`, is the canonical map at `(F, G[n])` preceded by
the Hom-complex target shift. -/
theorem homComplexToGlobalDerivedHom_shift_comp (F G : CochainComplex (SheafOfModules.{u}
  (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) [G.IsKInjective] (n : ℤ) :
    (((CategoryTheory.shiftFunctor (DerivedCategory AddCommGrpCat.{u}) n).map
              (homComplexToGlobalDerivedHom X F G) :
            (DerivedCategory.Q.obj (F.HomComplex G))⟦n⟧ ⟶
              ((derivedModuleGlobalSections X).obj
                (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj F))).obj
                  (DerivedCategory.Q.obj G)))⟦n⟧) ≫
          ((((derivedModuleGlobalSections X).commShiftIso n).app
                (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj F))).obj
                  (DerivedCategory.Q.obj G))).inv ≫
            (derivedModuleGlobalSections X).map
              (derivedSheafHomTargetShiftIso X (DerivedCategory.Q.obj F)
                (DerivedCategory.Q.obj G) n).inv)) ≫
        (derivedModuleGlobalSections X).map
          (((derivedSheafHomBifunctor X).map (𝟙 (DerivedCategory.Q.obj F)).op).app
              ((DerivedCategory.Q.obj G)⟦n⟧) ≫
            ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj F))).map
              ((DerivedCategory.Q.commShiftIso n).inv.app G)) =
      (DerivedCategory.Q.commShiftIso n).inv.app (F.HomComplex G) ≫
        DerivedCategory.Q.map (homComplexTargetShiftIso F G n).hom ≫
          (homComplexToGlobalDerivedHom X F (G⟦n⟧) :
            DerivedCategory.Q.obj (F.HomComplex (G⟦n⟧)) ⟶
              (derivedModuleGlobalSections X).obj
                (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj F))).obj
                  (DerivedCategory.Q.obj (G⟦n⟧)))) := by
  have hW : (derivedSheafHomTargetShiftIso X (DerivedCategory.Q.obj F)
          (DerivedCategory.Q.obj G) n).inv ≫
        (((derivedSheafHomBifunctor X).map (𝟙 (DerivedCategory.Q.obj F)).op).app
            ((DerivedCategory.Q.obj G)⟦n⟧) ≫
          ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj F))).map
            ((DerivedCategory.Q.commShiftIso n).inv.app G)) =
      (derivedSheafHomTargetShiftIsoOfKInjective X F G n).inv := by
    rw [Iso.inv_comp_eq, ← derivedSheafHomTargetShiftIso_eq_ofKInjective X F G n,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [Category.assoc, Category.assoc, ← CategoryTheory.Functor.map_comp, hW,
    show ((((derivedModuleGlobalSections X).commShiftIso n).app
            (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj F))).obj
              (DerivedCategory.Q.obj G))).inv ≫
          (derivedModuleGlobalSections X).map
            (derivedSheafHomTargetShiftIsoOfKInjective X F G n).inv) =
        (globalDerivedHomTargetShiftIsoOfKInjective X F G n).inv from rfl]
  exact comp_inv_eq_of_comp_hom_eq ((DerivedCategory.Q.commShiftIso n).app (F.HomComplex G)) _
    (DerivedCategory.Q.map (homComplexTargetShiftIso F G n).hom) _ _
      (homComplexToGlobalDerivedHom_shift_iso X F G n)

/-- **The degree-`n` reading of the canonical map is the degree-zero reading at the pair
`(F, G[n])`.** The degree-`n` cohomology of the canonical map, read through the degree-`n`
identification of the global derived hom and then transported from `(Q G)[n]` to `Q (G[n])`, is
the degree-zero cohomology of the canonical map at `(F, G[n])` read through Tag 08JA, applied to
the class of `η` moved into degree zero by the shift sequence of the homology functors of
`D(Ab)`. -/
theorem globalDerivedHomDegreeEquiv_homologyMap_eq_degreeZero (F G : CochainComplex
  (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) [G.IsKInjective]
    (n : ℤ)
    (η : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
      (DerivedCategory.Q.obj (F.HomComplex G)) : Type u)) :
    globalDerivedHomDegreeEquiv X (DerivedCategory.Q.obj F) (DerivedCategory.Q.obj G) n
          ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
            (homComplexToGlobalDerivedHom X F G) η) ≫
        (DerivedCategory.Q.commShiftIso n).inv.app G =
      derivedSheafHomGlobalSectionsEquiv X (DerivedCategory.Q.obj F)
        (DerivedCategory.Q.obj (G⟦n⟧))
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((DerivedCategory.Q.commShiftIso n).inv.app (F.HomComplex G) ≫
            DerivedCategory.Q.map (homComplexTargetShiftIso F G n).hom ≫
              homComplexToGlobalDerivedHom X F (G⟦n⟧))
          ((((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).isoShift n).inv.app
        (DerivedCategory.Q.obj (F.HomComplex G))) η)) := by
  have ha : (((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).isoShift n).inv.app
        ((derivedModuleGlobalSections X).obj (((derivedSheafHomBifunctor X).obj (op
          (DerivedCategory.Q.obj F))).obj (DerivedCategory.Q.obj G))))
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
          (homComplexToGlobalDerivedHom X F G) η) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((CategoryTheory.shiftFunctor (DerivedCategory AddCommGrpCat.{u}) n).map
          (homComplexToGlobalDerivedHom X F G)) ((((DerivedCategory.homologyFunctor
            AddCommGrpCat.{u} 0).isoShift n).inv.app
        (DerivedCategory.Q.obj (F.HomComplex G))) η) :=
    ConcreteCategory.congr_hom
      (CategoryTheory.Functor.isoShift_inv_naturality
        (F := DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0) n
        (homComplexToGlobalDerivedHom X F G)) η
  refine (congrArg (fun z => z ≫ (DerivedCategory.Q.commShiftIso n).inv.app G)
    (globalDerivedHomDegreeEquiv_apply X (DerivedCategory.Q.obj F) (DerivedCategory.Q.obj G) n
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
        (homComplexToGlobalDerivedHom X F G) η))).trans ?_
  refine (congrArg (fun z => derivedSheafHomGlobalSectionsEquiv X (DerivedCategory.Q.obj F)
      ((DerivedCategory.Q.obj G)⟦n⟧)
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map ((((derivedModuleGlobalSections
        X).commShiftIso n).app (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj
        F))).obj (DerivedCategory.Q.obj G))).inv ≫
          (derivedModuleGlobalSections X).map
            (derivedSheafHomTargetShiftIso X (DerivedCategory.Q.obj F)
              (DerivedCategory.Q.obj G) n).inv) z) ≫
    (DerivedCategory.Q.commShiftIso n).inv.app G) ha).trans ?_
  refine (congrArg (fun z => derivedSheafHomGlobalSectionsEquiv X (DerivedCategory.Q.obj F)
      ((DerivedCategory.Q.obj G)⟦n⟧) z ≫
    (DerivedCategory.Q.commShiftIso n).inv.app G)
    (homologyZero_map_comp_apply ((CategoryTheory.shiftFunctor (DerivedCategory AddCommGrpCat.{u})
      n).map
            (homComplexToGlobalDerivedHom X F G) :
          (DerivedCategory.Q.obj (F.HomComplex G))⟦n⟧ ⟶
            ((derivedModuleGlobalSections X).obj (((derivedSheafHomBifunctor X).obj (op
              (DerivedCategory.Q.obj F))).obj (DerivedCategory.Q.obj G)))⟦n⟧)
              ((((derivedModuleGlobalSections X).commShiftIso n).app (((derivedSheafHomBifunctor
              X).obj (op (DerivedCategory.Q.obj F))).obj (DerivedCategory.Q.obj G))).inv ≫
          (derivedModuleGlobalSections X).map
            (derivedSheafHomTargetShiftIso X (DerivedCategory.Q.obj F)
              (DerivedCategory.Q.obj G) n).inv) ((((DerivedCategory.homologyFunctor
                AddCommGrpCat.{u} 0).isoShift n).inv.app
        (DerivedCategory.Q.obj (F.HomComplex G))) η))).trans ?_
  refine (Category.id_comp _).symm.trans ?_
  refine (derivedSheafHomGlobalSectionsEquiv_naturality X (𝟙 (DerivedCategory.Q.obj F))
    ((DerivedCategory.Q.commShiftIso n).inv.app G)
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
      (((CategoryTheory.shiftFunctor (DerivedCategory AddCommGrpCat.{u}) n).map
            (homComplexToGlobalDerivedHom X F G) :
          (DerivedCategory.Q.obj (F.HomComplex G))⟦n⟧ ⟶
            ((derivedModuleGlobalSections X).obj (((derivedSheafHomBifunctor X).obj (op
              (DerivedCategory.Q.obj F))).obj (DerivedCategory.Q.obj G)))⟦n⟧) ≫
              ((((derivedModuleGlobalSections X).commShiftIso n).app (((derivedSheafHomBifunctor
              X).obj (op (DerivedCategory.Q.obj F))).obj (DerivedCategory.Q.obj G))).inv ≫
          (derivedModuleGlobalSections X).map
            (derivedSheafHomTargetShiftIso X (DerivedCategory.Q.obj F)
              (DerivedCategory.Q.obj G) n).inv)) ((((DerivedCategory.homologyFunctor
                AddCommGrpCat.{u} 0).isoShift n).inv.app
        (DerivedCategory.Q.obj (F.HomComplex G))) η))).symm.trans ?_
  refine (congrArg (fun z => derivedSheafHomGlobalSectionsEquiv X (DerivedCategory.Q.obj F)
      (DerivedCategory.Q.obj (G⟦n⟧)) z)
    (homologyZero_map_comp_apply (((CategoryTheory.shiftFunctor (DerivedCategory
      AddCommGrpCat.{u}) n).map
            (homComplexToGlobalDerivedHom X F G) :
          (DerivedCategory.Q.obj (F.HomComplex G))⟦n⟧ ⟶
            ((derivedModuleGlobalSections X).obj (((derivedSheafHomBifunctor X).obj (op
              (DerivedCategory.Q.obj F))).obj (DerivedCategory.Q.obj G)))⟦n⟧) ≫
              ((((derivedModuleGlobalSections X).commShiftIso n).app (((derivedSheafHomBifunctor
              X).obj (op (DerivedCategory.Q.obj F))).obj (DerivedCategory.Q.obj G))).inv ≫
          (derivedModuleGlobalSections X).map
            (derivedSheafHomTargetShiftIso X (DerivedCategory.Q.obj F)
              (DerivedCategory.Q.obj G) n).inv)) ((derivedModuleGlobalSections X).map
          (((derivedSheafHomBifunctor X).map (𝟙 (DerivedCategory.Q.obj F)).op).app
              ((DerivedCategory.Q.obj G)⟦n⟧) ≫
            ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj F))).map
              ((DerivedCategory.Q.commShiftIso n).inv.app G))) ((((DerivedCategory.homologyFunctor
                AddCommGrpCat.{u} 0).isoShift n).inv.app
        (DerivedCategory.Q.obj (F.HomComplex G))) η))).trans ?_
  exact congrArg (fun z : (DerivedCategory.Q.obj (F.HomComplex G))⟦n⟧ ⟶
        (derivedModuleGlobalSections X).obj (((derivedSheafHomBifunctor X).obj (op
          (DerivedCategory.Q.obj F))).obj (DerivedCategory.Q.obj (G⟦n⟧))) =>
      derivedSheafHomGlobalSectionsEquiv X (DerivedCategory.Q.obj F)
        (DerivedCategory.Q.obj (G⟦n⟧))
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map z
          ((((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).isoShift n).inv.app
        (DerivedCategory.Q.obj (F.HomComplex G))) η)))
    (homComplexToGlobalDerivedHom_shift_comp X F G n)

/-- **The canonical map `Hom^•(F, G) ⟶ RHom_O(F, G)` is the localization functor on degree-`n`
cohomology, at a K-flat source and a K-injective target.** The degree-`n` cohomology of
`Hom^•(F, G)` is `Hom_{K(O)}(F, G[n])` by Tag 0A8Z, the degree-`n` cohomology of `RHom_O(F, G)`
is `Hom_{D(O)}(Q F, (Q G)[n])` by Tag 0B6E
(`AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv`), and the map between them induced by
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom` is the localization functor
`K(O) ⥤ D(O)`, read on a K-injective target by
`AlgebraicGeometry.RingedSite.homotopyHomDerivedCategoryEquiv`. -/
theorem homComplexToGlobalDerivedHom_homology_of_isKFlat (F G : CochainComplex (SheafOfModules.{u}
  (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hF : Stacks.SheafOfModules.IsKFlat X.O F) [G.IsKInjective] (n : ℤ)
    (η : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
      (DerivedCategory.Q.obj (F.HomComplex G)) : Type u)) :
    globalDerivedHomDegreeEquiv X (DerivedCategory.Q.obj F) (DerivedCategory.Q.obj G) n
          ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
            (homComplexToGlobalDerivedHom X F G) η) ≫
        (DerivedCategory.Q.commShiftIso n).inv.app G =
      homotopyHomDerivedCategoryEquiv F (G⟦n⟧)
        ((𝟙 _ ≫ CohomologyClass.homAddEquiv (homologyAddEquiv F (G⟦n⟧) 0
              (((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).app
                (F.HomComplex (G⟦n⟧))).hom ((DerivedCategory.homologyFunctor AddCommGrpCat.{u}
                  0).map ((DerivedCategory.Q.commShiftIso n).inv.app (F.HomComplex G) ≫
          DerivedCategory.Q.map (homComplexTargetShiftIso F G n).hom)
            ((((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).isoShift n).inv.app
        (DerivedCategory.Q.obj (F.HomComplex G))) η))))) ≫
          (HomotopyCategory.quotient
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
              (ComplexShape.up ℤ)).map
            ((shiftFunctorZero
                (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
                ℤ).app
              (G⟦n⟧)).hom) := by
  refine (globalDerivedHomDegreeEquiv_homologyMap_eq_degreeZero X F G n η).trans ?_
  refine (congrArg (fun z => derivedSheafHomGlobalSectionsEquiv X (DerivedCategory.Q.obj F)
      (DerivedCategory.Q.obj (G⟦n⟧))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map z
        ((((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).isoShift n).inv.app
        (DerivedCategory.Q.obj (F.HomComplex G))) η)))
    (Category.assoc ((DerivedCategory.Q.commShiftIso n).inv.app (F.HomComplex G))
      (DerivedCategory.Q.map (homComplexTargetShiftIso F G n).hom)
      (homComplexToGlobalDerivedHom X F (G⟦n⟧))).symm).trans ?_
  refine (congrArg (fun z => derivedSheafHomGlobalSectionsEquiv X (DerivedCategory.Q.obj F)
      (DerivedCategory.Q.obj (G⟦n⟧)) z)
    (homologyZero_map_comp_apply ((DerivedCategory.Q.commShiftIso n).inv.app (F.HomComplex G) ≫
          DerivedCategory.Q.map (homComplexTargetShiftIso F G n).hom)
            (homComplexToGlobalDerivedHom X F (G⟦n⟧)) ((((DerivedCategory.homologyFunctor
            AddCommGrpCat.{u} 0).isoShift n).inv.app
        (DerivedCategory.Q.obj (F.HomComplex G))) η)).symm).trans ?_
  refine (derivedSheafHomGlobalSectionsEquiv_eq_ofKFlat X F (G⟦n⟧) hF _).trans ?_
  exact homComplexToGlobalDerivedHom_homology_zero_of_isKFlat X F (G⟦n⟧) hF
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map ((DerivedCategory.Q.commShiftIso
    n).inv.app (F.HomComplex G) ≫
          DerivedCategory.Q.map (homComplexTargetShiftIso F G n).hom)
            ((((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).isoShift n).inv.app
        (DerivedCategory.Q.obj (F.HomComplex G))) η))

end AlgebraicGeometry.RingedSite

end
