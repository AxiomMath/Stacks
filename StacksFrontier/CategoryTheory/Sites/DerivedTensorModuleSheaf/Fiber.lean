module

public import Mathlib.CategoryTheory.Sites.Point.Monoidal
public import StacksFrontier.Algebra.Homology.MapHomologicalComplexExactness
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.ChangeOfRings
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Constant
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Monoidal
public import StacksFrontier.CategoryTheory.Sites.Point.ConstantSheafFiber

/-!
# Fibres of K-flat complexes of sheaves of modules at a point of a site

Let `(C, J)` be a site, `Φ` a point of it and `Λ` a commutative ring. The fibre functor
`F ↦ F_Φ` from sheaves of `Λ`-modules to `Λ`-modules is exact and monoidal, and the fibre of a
constant sheaf `\underline{M}` is `M`. Consequently the fibre of a K-flat complex of sheaves of
`Λ`-modules is a K-flat complex of `Λ`-modules: for an acyclic complex `M` of `Λ`-modules the
complex `Tot(\underline{M} ⊗ P)` is acyclic, and its fibre is `Tot(M ⊗ P_Φ)`.

## Main definitions

* `Stacks.ModuleSheaf.moduleSheafFiber`: the fibre functor at a point on sheaves of
  `Λ`-modules; it is exact and additive.

## Main results

* `Stacks.ModuleSheaf.sheafFiberTotalComplexIso`: the fibre of a total tensor complex is the
  total tensor complex of the fibres.
* `Stacks.ModuleSheaf.kFlat_sheafFiber`: the fibre of a K-flat complex is K-flat.
* `Stacks.ModuleSheaf.sheafFiberExtendScalarsIso`: the fibre of an extension of scalars is the
  extension of scalars of the fibre.

## Implementation notes

This is part (1) of [Stacks, Tag 0DEN] for sheaves of modules over a constant ring, on a site of
arbitrary size; `Stacks.Sheaves.KFlatStalkCriterion.kFlatStalk_of_kFlat_unconditional` is the
same statement for sheaves of modules over a sheaf of rings on a site whose objects, morphisms
and sections share one universe.

## References

* [Stacks Project, Tag 0DEN](https://stacks.math.columbia.edu/tag/0DEN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CochainComplex.KFlatBifunctor

universe w v u

namespace Stacks.ModuleSheaf

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory monoidalClosed

variable {Λ : Type w} [CommRing Λ]

/-- Tensoring on the right with a module commutes with filtered colimits. -/
instance preservesFilteredColimitsOfSize_tensorRight_moduleCat (X : ModuleCat.{w} Λ) :
    PreservesFilteredColimitsOfSize.{w, w} (tensorRight X) :=
  ⟨fun _ _ _ => preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)⟩

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [UnivLE.{max u v, w}]
  [LocallySmall.{w} C] (Φ : J.Point.{w})

variable (Λ) in
/-- The fibre functor at `Φ` on sheaves of `Λ`-modules. -/
abbrev moduleSheafFiber : Sheaf J (ModuleCat.{w} Λ) ⥤ ModuleCat.{w} Λ := Φ.sheafFiber

/-- The fibre functor at `Φ` on sheaves of `Λ`-modules preserves finite limits. -/
instance : PreservesFiniteLimits (moduleSheafFiber Λ Φ) :=
  inferInstanceAs (PreservesFiniteLimits (Φ.sheafFiber (A := ModuleCat.{w} Λ)))

/-- The fibre functor at `Φ` on sheaves of `Λ`-modules preserves finite colimits. -/
instance : PreservesFiniteColimits (moduleSheafFiber Λ Φ) :=
  inferInstanceAs (PreservesFiniteColimits (Φ.sheafFiber (A := ModuleCat.{w} Λ)))

/-- The fibre functor at `Φ` on sheaves of `Λ`-modules is additive. -/
instance : (moduleSheafFiber Λ Φ).Additive := by
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (moduleSheafFiber Λ Φ)
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (moduleSheafFiber Λ Φ)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The fibre at a point of a total tensor complex of complexes of sheaves of `Λ`-modules is the
total tensor complex of the fibres. -/
def sheafFiberTotalComplexIso (K L : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ) :
    ((moduleSheafFiber Λ Φ).mapHomologicalComplex _).obj
        (totalComplex (curriedTensor _) K L) ≅
      totalComplex (curriedTensor _)
        (((moduleSheafFiber Λ Φ).mapHomologicalComplex _).obj K)
        (((moduleSheafFiber Λ Φ).mapHomologicalComplex _).obj L) :=
  Functor.mapBifunctorTotalIso (curriedTensor _) (curriedTensor _) (moduleSheafFiber Λ Φ)
    (moduleSheafFiber Λ Φ) (moduleSheafFiber Λ Φ)
    (fun A B => (Functor.Monoidal.μIso (moduleSheafFiber Λ Φ) A B).symm)
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (fun f B => by simp) (fun A _ _ g => by simp)
    K L

/-- **The fibre of a K-flat complex is K-flat.** If `P` is a K-flat complex of sheaves of
`Λ`-modules, then its fibre at a point of the site is a K-flat complex of `Λ`-modules. -/
theorem kFlat_sheafFiber {P : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ}
    (hP : KFlat (curriedTensor _) P) :
    KFlat (curriedTensor _) (((moduleSheafFiber Λ Φ).mapHomologicalComplex _).obj P) := by
  intro M hM
  let c := constantSheaf J (ModuleCat.{w} Λ)
  have : PreservesFiniteColimits c := by
    unfold c constantSheaf
    infer_instance
  have : PreservesFiniteLimits c := preservesFiniteLimits_constantSheaf J Λ
  have : c.Additive := Functor.additive_of_preserves_binary_products _
  let eM : ((moduleSheafFiber Λ Φ).mapHomologicalComplex _).obj
      ((c.mapHomologicalComplex _).obj M) ≅ M :=
    (Functor.mapHomologicalComplexCompIso (Sites.constantSheafFiberNatIso Φ) _).app M ≪≫
      (Functor.mapHomologicalComplexIdIso (ModuleCat.{w} Λ) _).app M
  let e := sheafFiberTotalComplexIso Φ ((c.mapHomologicalComplex _).obj M) P ≪≫
    (((curriedTensor _).map₂HomologicalComplex _ _ _).mapIso eM).app _
  exact fun i => ((hP _ (fun i => (hM i).map c) i).map (moduleSheafFiber Λ Φ)).of_iso e

/-- **The fibre of an extension of scalars is the extension of scalars of the fibre.** For a
ring homomorphism `f : Λ →+* S`, the fibre at `Φ` of the sheafification of `U ↦ S ⊗_Λ F(U)` is
`S ⊗_Λ F_Φ`. -/
def sheafFiberExtendScalarsIso {S : Type w} [CommRing S] (f : Λ →+* S) :
    extendScalars J f ⋙ moduleSheafFiber S Φ ≅
      moduleSheafFiber Λ Φ ⋙ ModuleCat.extendScalars.{w, w, w} f :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (Φ.presheafToSheafCompSheafFiberIso (ModuleCat.{w} S))) ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf J (ModuleCat.{w} Λ))
      (Φ.presheafFiberCompIso (ModuleCat.extendScalars.{w, w, w} f)) ≪≫
    (Functor.associator _ _ _).symm

end Stacks.ModuleSheaf
