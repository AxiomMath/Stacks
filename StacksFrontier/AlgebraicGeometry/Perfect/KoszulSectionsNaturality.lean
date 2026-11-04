module

public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOverAnObjectNaturality

/-!
# Naturality of the identification of sections with morphisms from the structure sheaf

For an open `U` of a space carrying a sheaf of commutative rings, the identification
`Hom_{D(O_U)}(O_U, E|_U) ≅ H⁰(U, E)` is natural in the object `E` of `D(O_X)`: postcomposing a
morphism `O_U ⟶ E|_U` with the restriction of `g : E ⟶ E'` corresponds to the map induced by `g`
on degree-zero hypercohomology over `U`.

## Main results

* `Koszul.DerivedSystem.sectionsEquiv_naturality`: the identification
  `Hom_{D(O_U)}(O_U, E|_U) ≅ H⁰(U, E)` is natural in `E`.
* `Koszul.DerivedSystem.sectionsEquivOfUnion_naturality`: the same statement over the union
  `U = D(f₁) ∪ ⋯ ∪ D(f_r)` of the basic opens of a finite sequence of elements of a ring.

## Implementation notes

The identification is a composite of four steps: transport along the comparison of the two
models of derived restriction to an open, the morphism-group isomorphism induced by the
equivalence between the slice-site and the open-subspace model of `O_U`-modules, the
identification of hypercohomology of a derived internal Hom with a morphism group, and the
identification of the derived internal Hom out of the structure sheaf with the identity.  The
first two are isolated as statements about an arbitrary natural isomorphism and an arbitrary
fully faithful functor, and the last two as a statement about an arbitrary ringed site; this
keeps the rewrites type-correct without relaxing the transparency used for unification.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open ExtensionByZeroModules Stacks.Cohomology.OpenSubspace
open Stacks.SheafOfModules (StructureSheafModules ringedSite derivedRestrict
  sliceToSubspaceFunctor derivedRestrictToSubspaceIso)

universe u

namespace Koszul.DerivedSystem

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Morphism groups under isomorphisms and fully faithful functors -/

private lemma homCongrAddEquiv_apply {C : Type*} [Category C] [Preadditive C] {X X' Y Y' : C}
    (i : X ≅ X') (j : Y ≅ Y') (a : X ⟶ Y) :
    homCongrAddEquiv i j a = i.inv ≫ a ≫ j.hom := rfl

private lemma mapHomAddEquiv_symm_apply {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful] (X Y : C)
    (b : F.obj X ⟶ F.obj Y) :
    (mapHomAddEquiv F X Y).symm b = F.preimage b := rfl

/-- Transporting a morphism along the components of a natural isomorphism commutes with
postcomposition. -/
private lemma homCongrAddEquiv_naturality {C D : Type*} [Category C] [Category D]
    [Preadditive D] {F G : C ⥤ D} (ρ : F ≅ G) {O E E' : C} (g : E ⟶ E')
    (a : G.obj O ⟶ G.obj E) :
    homCongrAddEquiv (ρ.app O).symm (ρ.app E').symm (a ≫ G.map g) =
      homCongrAddEquiv (ρ.app O).symm (ρ.app E).symm a ≫ F.map g := by
  simp only [homCongrAddEquiv_apply, Iso.symm_inv, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Category.assoc]
  rw [ρ.inv.naturality g]

/-- The inverse of the isomorphism of morphism groups induced by a fully faithful functor
commutes with postcomposition. -/
private lemma mapHomAddEquiv_symm_naturality {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    {O E E' : C} (g : E ⟶ E') (b : F.obj O ⟶ F.obj E) :
    (mapHomAddEquiv F O E').symm (b ≫ F.map g) = (mapHomAddEquiv F O E).symm b ≫ g := by
  simp only [mapHomAddEquiv_symm_apply]
  apply F.map_injective
  rw [F.map_preimage, F.map_comp, F.map_preimage]

/-- Reading a morphism through the components of a natural isomorphism `P ⋙ T ≅ G` and then
through the fully faithful functor `T` commutes with postcomposition. -/
private lemma transport_naturality {B C D : Type*} [Category B] [Category C] [Category D]
    [Preadditive C] [Preadditive D] (T : C ⥤ D) [T.Additive] [T.Full] [T.Faithful] (P : B ⥤ C)
    {G : B ⥤ D} (ρ : P ⋙ T ≅ G) {O E E' : B} (g : E ⟶ E') (a : G.obj O ⟶ G.obj E) :
    (mapHomAddEquiv T (P.obj O) (P.obj E')).symm
        (homCongrAddEquiv (ρ.app O).symm (ρ.app E').symm (a ≫ G.map g)) =
      (mapHomAddEquiv T (P.obj O) (P.obj E)).symm
          (homCongrAddEquiv (ρ.app O).symm (ρ.app E).symm a) ≫ P.map g := by
  rw [homCongrAddEquiv_naturality ρ g a]
  exact mapHomAddEquiv_symm_naturality T (P.map g) _

/-! ### Sections over an object of a ringed site -/

section RingedSiteStep

variable (Y : RingedSite.{u, u, u}) (V : Y.C)
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  [PreservesFiniteLimits (SheafOfModules.overFunctor.{u} (ringSheaf Y.O) V)]
  [PreservesFiniteColimits (SheafOfModules.overFunctor.{u} (ringSheaf Y.O) V)]

/-- Reading a morphism `O|_V ⟶ E|_V` of `D(O|_V)` as a degree-zero hypercohomology class over an
object `V` of a ringed site commutes with postcomposing by the restriction of `g : E ⟶ E'`. -/
private lemma ringedSiteStep (E E' : DerivedCategory (SheafOfModules.{u} (ringSheaf Y.O)))
    (g : E ⟶ E')
    (c : (SheafOfModules.overFunctor.{u} (ringSheaf Y.O) V).mapDerivedCategory.obj
        (RingedSite.derivedStructureSheaf Y) ⟶
      (SheafOfModules.overFunctor.{u} (ringSheaf Y.O) V).mapDerivedCategory.obj E) :
    ((Stacks.Cohomology.Localization.derivedSectionsOverObject Y V ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).mapIso
        ((RingedSite.derivedStructureSheafHomNatIso Y).app E')).addCommGroupIsoToAddEquiv
        ((RingedSite.derivedSheafHomSectionsEquiv Y V
            (RingedSite.derivedStructureSheaf Y) E').symm
          (c ≫ (SheafOfModules.overFunctor.{u} (ringSheaf Y.O) V).mapDerivedCategory.map g)) =
      ((Stacks.Cohomology.Localization.derivedSectionsOverObject Y V ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map g).hom
        (((Stacks.Cohomology.Localization.derivedSectionsOverObject Y V ⋙
              DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).mapIso
            ((RingedSite.derivedStructureSheafHomNatIso Y).app E)).addCommGroupIsoToAddEquiv
          ((RingedSite.derivedSheafHomSectionsEquiv Y V
            (RingedSite.derivedStructureSheaf Y) E).symm c)) := by
  have hnat := RingedSite.derivedSheafHomSectionsEquiv_naturality Y V
    (𝟙 (RingedSite.derivedStructureSheaf Y)) g
    ((RingedSite.derivedSheafHomSectionsEquiv Y V (RingedSite.derivedStructureSheaf Y) E).symm c)
  have hmor : (SheafOfModules.overFunctor.{u} (ringSheaf Y.O) V).mapDerivedCategory.map
          (𝟙 (RingedSite.derivedStructureSheaf Y)) ≫
        (RingedSite.derivedSheafHomSectionsEquiv Y V (RingedSite.derivedStructureSheaf Y) E)
            ((RingedSite.derivedSheafHomSectionsEquiv Y V
              (RingedSite.derivedStructureSheaf Y) E).symm c) ≫
          (SheafOfModules.overFunctor.{u} (ringSheaf Y.O) V).mapDerivedCategory.map g =
      c ≫ (SheafOfModules.overFunctor.{u} (ringSheaf Y.O) V).mapDerivedCategory.map g := by
    rw [AddEquiv.apply_symm_apply, CategoryTheory.Functor.map_id, Category.id_comp]
  have hsections := (AddEquiv.eq_symm_apply _).mpr (hnat.trans hmor)
  have hcomp : (Stacks.Cohomology.Localization.derivedSectionsOverObject Y V ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((Functor.uncurry.obj (RingedSite.derivedSheafHomBifunctor Y)).map
            (((𝟙 (RingedSite.derivedStructureSheaf Y)).op, g) :
              ((op (RingedSite.derivedStructureSheaf Y), E) :
                (DerivedCategory (SheafOfModules.{u} (ringSheaf Y.O)))ᵒᵖ ×
                  DerivedCategory (SheafOfModules.{u} (ringSheaf Y.O))) ⟶
              (op (RingedSite.derivedStructureSheaf Y), E'))) ≫
        ((Stacks.Cohomology.Localization.derivedSectionsOverObject Y V ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).mapIso
            ((RingedSite.derivedStructureSheafHomNatIso Y).app E')).hom =
      ((Stacks.Cohomology.Localization.derivedSectionsOverObject Y V ⋙
            DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).mapIso
          ((RingedSite.derivedStructureSheafHomNatIso Y).app E)).hom ≫
        (Stacks.Cohomology.Localization.derivedSectionsOverObject Y V ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map g := by
    have hu : (Functor.uncurry.obj (RingedSite.derivedSheafHomBifunctor Y)).map
          (((𝟙 (RingedSite.derivedStructureSheaf Y)).op, g) :
            ((op (RingedSite.derivedStructureSheaf Y), E) :
              (DerivedCategory (SheafOfModules.{u} (ringSheaf Y.O)))ᵒᵖ ×
                DerivedCategory (SheafOfModules.{u} (ringSheaf Y.O))) ⟶
            (op (RingedSite.derivedStructureSheaf Y), E')) =
        ((RingedSite.derivedSheafHomBifunctor Y).obj
          (op (RingedSite.derivedStructureSheaf Y))).map g := by
      simp
    simp only [Functor.mapIso_hom, Iso.app_hom, ← Functor.map_comp, hu]
    congr 1
    exact (RingedSite.derivedStructureSheafHomNatIso Y).hom.naturality g
  rw [← hsections]
  exact ConcreteCategory.congr_hom hcomp _

end RingedSiteStep

/-! ### Naturality of sections as morphisms out of the structure sheaf -/

section Sections

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X) (U : Opens X)

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive

attribute [local instance] hasMapBifunctorSheafTensor preservesFiniteLimitsOver
  preservesFiniteColimitsOver

/-- **The identification of sections over `U` with morphisms out of `O_U` is natural in the
module.** Postcomposing a morphism `O_U ⟶ E|_U` of `D(O_U)` with the restriction of
`g : E ⟶ E'` corresponds to the map induced by `g` on degree-zero hypercohomology over `U`. -/
theorem sectionsEquiv_naturality (E E' : DerivedCategory (StructureSheafModules Rc)) (g : E ⟶ E')
    (a : (derivedRestriction (structureSheaf Rc) U).obj
        (RingedSite.derivedStructureSheaf (ringedSite Rc)) ⟶
      (derivedRestriction (structureSheaf Rc) U).obj E) :
    sectionsEquiv Rc U E' (a ≫ (derivedRestriction (structureSheaf Rc) U).map g) =
      ((sectionsDegreeZero Rc U).map g).hom (sectionsEquiv Rc U E a) := by
  simp only [sectionsEquiv, AddEquiv.trans_apply]
  rw [transport_naturality (sliceToSubspaceFunctor Rc U).mapDerivedCategory (derivedRestrict Rc U)
      (derivedRestrictToSubspaceIso Rc U)
      (O := RingedSite.derivedStructureSheaf (ringedSite Rc)) g a]
  let : PreservesFiniteLimits (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (ringedSite Rc).O) U) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits U
  let : PreservesFiniteColimits (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (ringedSite Rc).O) U) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits U
  exact ringedSiteStep (ringedSite Rc) U E E' g _

end Sections

variable {A : CommRingCat.{u}} {r : ℕ}

/-- **Sections as morphisms out of `O_U` are natural in the module, for the union
`U = D(f₁) ∪ ⋯ ∪ D(f_r)`.** Postcomposing `O_U ⟶ E|_U` with the restriction of `g : E ⟶ E'`
corresponds to the map induced by `g` on degree-zero hypercohomology over `U`. -/
theorem sectionsEquivOfUnion_naturality (f : Fin r → A)
    (E E' : derivedCat A) (g : E ⟶ E')
    (a : (restrictionToUnion f).obj (structureSheafObject A) ⟶ (restrictionToUnion f).obj E) :
    sectionsEquivOfUnion f E' (a ≫ (restrictionToUnion f).map g) =
      ((sectionsOnUnion f).map g).hom (sectionsEquivOfUnion f E a) :=
  sectionsEquiv_naturality (Spec A).sheaf (unionOfBasicOpens f) E E' g a

end Koszul.DerivedSystem

end
