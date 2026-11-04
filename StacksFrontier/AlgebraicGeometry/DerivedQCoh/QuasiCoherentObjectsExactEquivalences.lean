module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiQuasicoherentRestriction
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineOpensChaoticQuasicoherentEquality
public import StacksFrontier.AlgebraicGeometry.Topologies.ChaoticFlatQuasicoherent
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.CategoryTheory.Triangulated.LinearTriangulatedEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackAsATriangulatedFunctor
public import StacksFrontier.Homology.DerivedCategory.LocallySmall
import StacksCore.Tactic.StacksAttribute

/-!
# The five quasi-coherent derived categories of a scheme

Let `X` be a scheme in a big Zariski site. [Stacks, Tag 0GZZ] asserts canonical exact
equivalences between five triangulated categories:

1. `D_QCoh(𝒪_X)`, on the ringed space `(X, 𝒪_X)`;
2. `D_QCoh(X_Zar, 𝒪)`, on the small Zariski site of Topologies, Definition 020T;
3. `D_QCoh(X_{affine, Zar}, 𝒪)`, on the category of affine opens of `X` with the Zariski
   topology;
4. `D_QCoh(X_affine, 𝒪)`, on the same category with the chaotic topology;
5. `QC(X_affine, 𝒪)`, the quasi-coherent objects of Cohomology on Sites, Definition 0GYV.

This file proves all of it, as
`AlgebraicGeometry.Scheme.nonempty_quasicoherentDerived_linearTriangulatedEquivalences`: the five
subcategories are triangulated, and there are exact equivalences `(2) ≃ (1)`, `(1) ≃ (3)`,
`(4) ≃ (3)` and `(4) ≃ (5)` lying over the canonical functors, so any two of the five are
canonically exactly equivalent.

## Main definitions

* `Stacks.DerivedQCoh.linearTriangulatedEquivalenceOfCompιIso`: an equivalence of triangulated
  subcategories lying over an exact functor is an exact equivalence.
* `Stacks.DerivedQCoh.derivedCategoryBLinearTriangulatedEquivalence`: an equivalence of abelian
  categories matching two weak Serre classes `P`, `P'` restricts to an exact equivalence
  `D_P ≌ D_{P'}`.
* `AlgebraicGeometry.Scheme.smallZariskiQuasicoherentDerivedEquivalence`: `(2) ≃ (1)`, induced by
  the identification of modules of Descent, Remark 03FG.
* `AlgebraicGeometry.Scheme.affineZariskiQuasicoherentDerivedEquivalence`: `(1) ≃ (3)`, induced
  by restriction to the affine opens.
* `AlgebraicGeometry.Scheme.affineChaoticQuasicoherentDerivedEquivalence`: `(4) ≃ (3)`, the change
  of topology of Stacks 07A8, given by `Lε^*`.
* `AlgebraicGeometry.Scheme.affineChaoticQuasicoherentEquivQC`: `(4) ≃ (5)`.

## Main results

* `AlgebraicGeometry.Scheme.nonempty_quasicoherentDerived_linearTriangulatedEquivalences`:
  **Stacks 0GZZ.**

## Proof

The five steps of the source's proof, and where each is carried out:

* `(1) ≃ (2)`: modules on `(X_Zar, 𝒪)` and on `(X, 𝒪_X)` agree (03FG,
  `AlgebraicGeometry.smallZariskiModuleEquiv`), and the quasi-coherent ones correspond (03DX):
  `AlgebraicGeometry.SmallZariski.isQuasicoherentOnSite_iff_isQuasicoherent_restrictModule`.
* `(2) ≃ (3)`: the composite of `(2) ≃ (1)` and `(1) ≃ (3)`; the latter is restriction along the
  dense subsite of affine opens, matching quasi-coherent modules by
  `AlgebraicGeometry.Scheme.isQuasicoherentOnSite_affineOpensModuleRestriction_iff`.
* `(3) ≃ (4)`: Stacks 07A8 for `ε`, with Serre vanishing on affines (01XB) and the weak Serre
  property of the quasi-coherent modules (01LA) as inputs,
  `AlgebraicGeometry.Scheme.affineOpensChaoticDerivedEquivalence`, together with the equality of
  its image class with the quasi-coherent modules for the chaotic topology (0GZX, 0GZN),
  `AlgebraicGeometry.Scheme.imageOfLE_eq_isQuasicoherentOnSite_affineChaotic`. Its functor is
  `Lε^*`, which is exact (06YY), so the equivalence is exact.
* `(4) ≃ (5)`: the restriction maps between affine opens are flat, so Stacks 0GZR makes the two
  subcategories of `D(X_affine, 𝒪)` equal,
  `AlgebraicGeometry.affineChaotic_isQC_eq_hasQuasicoherentCohomology`.

Each subcategory `D_B` is triangulated because `B` is a weak Serre class (Stacks 06UP); `(4)`
and `(5)` are triangulated by Stacks 0GYW.

## Implementation notes

**Models of the derived categories.** `HasDerivedCategory` is a choice of localization, and the
library carries two for sheaves of modules on a small site: the locally small model, a global
instance, and `HasDerivedCategory.standard`, which is where Stacks 07A8 is constructed. Two models
of one category in scope defeat instance search, so this file erases the locally small instances
and reads every derived category of sheaves of modules at the standard model (the small Zariski
site, whose objects lie in `Type (u + 1)`, has no other model anyway). Derived categories of
presheaves of modules stay at the model of
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.DMod`, in which `QC` is defined.

**The sites.** Item (2) is the small Zariski site `AlgebraicGeometry.SmallZariski B X hX` of the
big Zariski site `B`, literally Topologies, Definition 020T (2), with structure sheaf
`U ↦ Γ(U, 𝒪_U)`. Items (3)–(5) use the category of affine opens of `X` with all inclusions as
arrows, which is how Section 0GZY describes `X_{affine, Zar}` ("the category of affine opens of
`X` with topology given by standard Zariski coverings"); its topology is induced from the opens of
`X` and its covering sieves are the Zariski coverings
(`AlgebraicGeometry.Scheme.mem_affineOpensTopology`), which generate the same topology as the
standard Zariski coverings. Packaging it on the affine opens of the space keeps it a
`RingedSite.{u, u, u}`, so that `D(X_affine, 𝒪)` and `QC(X_affine, 𝒪)` are formed with modules in
`Type u`, the universe of `𝒪_X`-modules; the copy built inside the big site has objects in
`Type (u + 1)`, for which the library forms `QC` only with modules in `Type (u + 1)`.

**`QC` and its base change.** `QC` is formed with
`AlgebraicGeometry.affineChaoticBaseChangeData`, the derived extension of scalars along the
restriction maps; a `BaseChangeData` is required to be left adjoint to derived restriction of
scalars, which determines it up to unique isomorphism.

## References

* [Stacks Project, Tag 0GZZ](https://stacks.math.columbia.edu/tag/0GZZ)
* [Stacks Project, Tag 03FG](https://stacks.math.columbia.edu/tag/03FG)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 07A8](https://stacks.math.columbia.edu/tag/07A8)
* [Stacks Project, Tag 0GZR](https://stacks.math.columbia.edu/tag/0GZR)
* [Stacks Project, Tag 06UP](https://stacks.math.columbia.edu/tag/06UP)
* [Stacks Project, Tag 0GYW](https://stacks.math.columbia.edu/tag/0GYW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w w' u v u' v'

namespace Stacks.DerivedQCoh

/-! ### Exact equivalences between triangulated subcategories -/

section Exact

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type u'} [Category.{v'} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **An equivalence of triangulated subcategories lying over an exact functor is exact.** Let
`P ⊆ C` and `Q ⊆ D` be triangulated subcategories, `F : C ⥤ D` an exact functor and
`e : P ≌ Q` an equivalence whose functor, followed by the inclusion of `Q`, is the inclusion of
`P` followed by `F`. Then `e` is an equivalence of triangulated categories: the shift structure
on its functor is the one read off from `F` through the fully faithful inclusion of `Q`. -/
def linearTriangulatedEquivalenceOfCompιIso (P : ObjectProperty C) (Q : ObjectProperty D)
    [P.IsTriangulated] [Q.IsTriangulated] (e : P.FullSubcategory ≌ Q.FullSubcategory)
    (F : C ⥤ D) [hF : F.CommShift ℤ] [hF' : F.IsTriangulated] (α : e.functor ⋙ Q.ι ≅ P.ι ⋙ F) :
    LinearTriangulatedEquivalence ℤ P.FullSubcategory Q.FullSubcategory :=
  letI : e.functor.CommShift ℤ := Functor.CommShift.ofComp α ℤ
  haveI : NatTrans.CommShift α.hom ℤ := Functor.CommShift.ofComp_compatibility α ℤ
  haveI : e.functor.IsTriangulated := (Functor.isTriangulated_iff_comp_right α).2 inferInstance
  { equivalence := e
    commShift := inferInstance
    isTriangulated := inferInstance
    linear := inferInstance }

/-- The underlying equivalence of `linearTriangulatedEquivalenceOfCompιIso` is the given one. -/
@[simp]
theorem linearTriangulatedEquivalenceOfCompιIso_equivalence (P : ObjectProperty C)
    (Q : ObjectProperty D) [P.IsTriangulated] [Q.IsTriangulated]
    (e : P.FullSubcategory ≌ Q.FullSubcategory) (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (α : e.functor ⋙ Q.ι ≅ P.ι ⋙ F) :
    (linearTriangulatedEquivalenceOfCompιIso P Q e F α).equivalence = e :=
  rfl

/-- **Equal triangulated subcategories are exactly equivalent**, by the identity on objects. -/
def linearTriangulatedEquivalenceOfEq {P Q : ObjectProperty C} [P.IsTriangulated]
    [Q.IsTriangulated] (h : P = Q) :
    LinearTriangulatedEquivalence ℤ P.FullSubcategory Q.FullSubcategory :=
  linearTriangulatedEquivalenceOfCompιIso P Q (ObjectProperty.equivOfEq h) (𝟭 C)
    (ObjectProperty.ιOfLECompιIso (le_of_eq h) ≪≫ (Functor.rightUnitor _).symm)

end Exact

/-! ### Exact abelian equivalences and `D_B` -/

section DerivedCategoryB

variable {A : Type u} [Category.{v} A] [Abelian A] {A' : Type u'} [Category.{v'} A'] [Abelian A']

/-- **`D_B(A)` is a triangulated subcategory for a weak Serre class `B`**, at every model of the
derived category: this is Stacks 06UP, `DerivedCategoryB.derivedCategoryB_isTriangulated`, with
the five-term form of the weak Serre condition supplied by
`WeakSerre.isWeakSerre_of_isWeakSerreClass`. -/
instance derivedCategoryB_isTriangulated_of_isWeakSerreClass [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsWeakSerreClass] :
    (DerivedCategoryB.derivedCategoryB P).IsTriangulated :=
  DerivedCategoryB.derivedCategoryB_isTriangulated P (WeakSerre.isWeakSerre_of_isWeakSerreClass P)

variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} A']

/-- **An equivalence of abelian categories matching two weak Serre classes induces an
equivalence of the corresponding subcategories of the derived categories.** If `E : A ≌ A'` is
an equivalence and `P'` is a weak Serre class with `P M ↔ P' (E M)`, then `E.mapDerivedCategory`
restricts to an equivalence `D_P(A) ≌ D_{P'}(A')`. -/
def derivedCategoryBEquivalence (E : A ≌ A') [E.functor.Additive] (P : ObjectProperty A)
    (P' : ObjectProperty A') [P'.IsWeakSerreClass] (h : ∀ M, P M ↔ P' (E.functor.obj M)) :
    (DerivedCategoryB.derivedCategoryB P).FullSubcategory ≌
      (DerivedCategoryB.derivedCategoryB P').FullSubcategory :=
  haveI := DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms P'
    (WeakSerre.isWeakSerre_of_isWeakSerreClass P')
  (Equivalence.mapDerivedCategory E).congrFullSubcategory (funext fun K ↦ propext <|
    forall_congr' fun n ↦
      (P'.prop_iff_of_iso ((E.functor.mapDerivedCategoryHomologyIso n).app K)).trans (h _).symm)

/-- The functor of `derivedCategoryBEquivalence`, followed by the inclusion of `D_{P'}(A')`, is
the inclusion of `D_P(A)` followed by `E.mapDerivedCategory`. -/
def derivedCategoryBEquivalenceFunctorCompιIso (E : A ≌ A') [E.functor.Additive]
    (P : ObjectProperty A) (P' : ObjectProperty A') [P'.IsWeakSerreClass]
    (h : ∀ M, P M ↔ P' (E.functor.obj M)) :
    (derivedCategoryBEquivalence E P P' h).functor ⋙ (DerivedCategoryB.derivedCategoryB P').ι ≅
      (DerivedCategoryB.derivedCategoryB P).ι ⋙ E.functor.mapDerivedCategory :=
  ObjectProperty.liftCompιIso _ _ _

/-- **`derivedCategoryBEquivalence` is an exact equivalence**: it lies over the exact functor
`E.mapDerivedCategory`. -/
def derivedCategoryBLinearTriangulatedEquivalence (E : A ≌ A') [E.functor.Additive]
    (P : ObjectProperty A) [P.IsWeakSerreClass] (P' : ObjectProperty A') [P'.IsWeakSerreClass]
    (h : ∀ M, P M ↔ P' (E.functor.obj M)) :
    LinearTriangulatedEquivalence ℤ (DerivedCategoryB.derivedCategoryB P).FullSubcategory
      (DerivedCategoryB.derivedCategoryB P').FullSubcategory :=
  linearTriangulatedEquivalenceOfCompιIso _ _ (derivedCategoryBEquivalence E P P' h)
    E.functor.mapDerivedCategory (derivedCategoryBEquivalenceFunctorCompιIso E P P' h)

/-- The underlying equivalence of `derivedCategoryBLinearTriangulatedEquivalence`. -/
@[simp]
theorem derivedCategoryBLinearTriangulatedEquivalence_equivalence (E : A ≌ A')
    [E.functor.Additive] (P : ObjectProperty A) [P.IsWeakSerreClass] (P' : ObjectProperty A')
    [P'.IsWeakSerreClass] (h : ∀ M, P M ↔ P' (E.functor.obj M)) :
    (derivedCategoryBLinearTriangulatedEquivalence E P P' h).equivalence =
      derivedCategoryBEquivalence E P P' h :=
  rfl

end DerivedCategoryB

/-! ### The standard model for sheaves of modules -/

/-- **The standard model of the derived category of sheaves of modules** on a small site, as a
declaration that can be installed as a local instance for sheaves of modules alone, leaving the
models chosen for other abelian categories (such as presheaves of modules) untouched. -/
abbrev sheafOfModulesStandardModel {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) [Abelian (SheafOfModules.{u} R)] :
    HasDerivedCategory.{u + 1} (SheafOfModules.{u} R) :=
  HasDerivedCategory.standard _

/-- **The standard model of the derived category of `𝒪_X`-modules** on a scheme `X`. -/
abbrev _root_.AlgebraicGeometry.Scheme.modulesStandardModel (X : AlgebraicGeometry.Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules :=
  HasDerivedCategory.standard _

end Stacks.DerivedQCoh

namespace AlgebraicGeometry

open Stacks.DerivedQCoh

/-! ### The change of topology `(3) ≃ (4)` at the standard model -/

section Chaotic

attribute [local instance] Stacks.DerivedQCoh.sheafOfModulesStandardModel
  Scheme.modulesStandardModel
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable (X : Scheme.{u})

/-- The coarsening `ε : (X_{affine, Zar}, 𝒪) ⟶ (X_affine, 𝒪)` of the Zariski topology on the
affine opens of `X` to the chaotic one, as a morphism of ringed topoi. -/
abbrev Scheme.affineCoarseningHom :=
  (X.affineZariskiRingedSite.coarseningHom
    (bot_le : (⊥ : GrothendieckTopology X.affineZariskiRingedSite.C) ≤
      X.affineZariskiRingedSite.J)).toRingedToposSiteHom

/-- The pullback along the coarsening `ε : (X_{affine, Zar}, 𝒪) ⟶ (X_affine, 𝒪)`, on the
homotopy category of complexes, has a left derived functor with respect to quasi-isomorphisms. -/
instance Scheme.hasLeftDerivedFunctor_affineCoarseningHom :
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.pullbackOnHomotopy
      X.affineCoarseningHom).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (X.affineZariskiRingedSite.ofLe bot_le).ringedTopos.O))
        (ComplexShape.up ℤ)) :=
  X.affineZariskiRingedSite.hasLeftDerivedFunctor_pullbackOnHomotopy_coarseningHom bot_le

/-- `Lε^* : D(X_affine, 𝒪) ⥤ D(X_{affine, Zar}, 𝒪)`, the derived pullback along the coarsening. -/
abbrev Scheme.affineCoarseningDerivedPullback :
    DerivedCategory (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O).ofLE
        (bot_le : (⊥ : GrothendieckTopology X.affineZariskiRingedSite.C) ≤
          X.affineZariskiRingedSite.J))) ⥤
      DerivedCategory (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O)) :=
  Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback.{u}
    (X := X.affineZariskiRingedSite.ringedTopos) X.affineCoarseningHom

/-- `Lε^*` commutes with the shifts, by Stacks 06YY. -/
instance Scheme.commShift_affineCoarseningDerivedPullback :
    X.affineCoarseningDerivedPullback.CommShift ℤ :=
  Stacks.Sheaves.RingedToposDerivedPullback.derivedPullback_commShift X.affineCoarseningHom

/-- `Lε^*` is an exact functor of triangulated categories, by Stacks 06YY: `ε^*` is exact, so it
inverts every quasi-isomorphism. -/
instance Scheme.isTriangulated_affineCoarseningDerivedPullback :
    X.affineCoarseningDerivedPullback.IsTriangulated :=
  Stacks.Sheaves.RingedToposDerivedPullback.derivedPullback_isTriangulated X.affineCoarseningHom
    (Stacks.Sheaves.RingedToposDerivedPullback.pullbackInvertsQuasiIso_isKFlat_of_exact
      X.affineCoarseningHom)

/-- The quasi-coherent modules on the chaotic affine site of `X` form a weak Serre subcategory:
the topology is chaotic and the restriction homomorphisms are flat, so Stacks 0GZP applies. -/
theorem Scheme.isWeakSerreClass_isQuasicoherentOnSite_affineChaotic :
    (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.affineChaoticRingedSite.O)).IsWeakSerreClass :=
  have : Fact (X.affineChaoticRingedSite.J = ⊥) := ⟨rfl⟩
  have : Fact (∀ {U V : X.affineChaoticRingedSite.Cᵒᵖ} (a : V ⟶ U),
      RingHom.Flat (X.affineChaoticRingedSite.O.obj.map a).hom) :=
    ⟨fun a ↦ flat_affineChaoticRingedSite_O_map X a⟩
  Stacks.Sheaves.ChaoticFlatQuasicoherent.isQuasicoherentOnSite_isWeakSerreClass.{u, u, u, u}
    X.affineChaoticRingedSite

/-- **The change of topology `(3) ≃ (4)` at the standard model, as an exact equivalence.** The
equivalence of Stacks 07A8 for the coarsening `ε` of the Zariski topology on the affine opens of
`X` to the chaotic one, `AlgebraicGeometry.Scheme.affineOpensChaoticDerivedEquivalence`, read
with item (4) as the quasi-coherent modules for the chaotic topology
(`AlgebraicGeometry.Scheme.imageOfLE_eq_isQuasicoherentOnSite_affineChaotic`). It lies over the
exact functor `Lε^*`, so it is an exact equivalence. -/
def Scheme.affineChaoticToZariskiStandard :
    haveI := X.isWeakSerreClass_isQuasicoherentOnSite_affineChaotic
    LinearTriangulatedEquivalence ℤ
      (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.affineChaoticRingedSite.O))).FullSubcategory
      X.affineOpensQuasicoherentDerivedCategory :=
  haveI := X.isWeakSerreClass_isQuasicoherentOnSite_affineChaotic
  let I : ObjectProperty (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.affineChaoticRingedSite.O)) :=
    Stacks.Cohomology.CompareTopologies.imageOfLE
      (bot_le : (⊥ : GrothendieckTopology X.affineZariskiRingedSite.C) ≤
        X.affineZariskiRingedSite.J)
      (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O)
      (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O))
  have hI : I = SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.affineChaoticRingedSite.O) :=
    X.imageOfLE_eq_isQuasicoherentOnSite_affineChaotic
  haveI : I.IsWeakSerreClass := hI ▸ X.isWeakSerreClass_isQuasicoherentOnSite_affineChaotic
  (linearTriangulatedEquivalenceOfEq (congrArg DerivedCategoryB.derivedCategoryB hI.symm)).trans
    (linearTriangulatedEquivalenceOfCompιIso _ _ X.affineOpensChaoticDerivedEquivalence
      X.affineCoarseningDerivedPullback (hF := X.commShift_affineCoarseningDerivedPullback)
      (hF' := X.isTriangulated_affineCoarseningDerivedPullback) (Iso.refl _))

open Stacks.ModulesOnACategory.QuasiCoherentCohomology in
/-- **Quasi-coherent cohomology on the chaotic affine site, on sheaves and on presheaves**, at the
standard model of the derived category of sheaves: a complex of sheaves of modules for the
chaotic topology has quasi-coherent cohomology sheaves if and only if the corresponding complex
of presheaves of modules lies in `qcohCohomologyProperty`. This is
`AlgebraicGeometry.Scheme.qcohCohomologyProperty_affineChaotic_iff` with the sheaf side read at
the standard model. -/
theorem Scheme.qcohCohomologyProperty_affineChaotic_iff_standard
    (K : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.affineChaoticRingedSite.O))) :
    qcohCohomologyProperty.{u} X.affineChaoticRingedSite
        (X.affineChaoticSheafPresheafEquivalence.functor.mapDerivedCategory.obj K) ↔
      DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.affineChaoticRingedSite.O)) K := by
  have hcomp := fun n : ℤ ↦
    (CategoryTheory.Functor.mapDerivedCategoryHomologyIso
      X.affineChaoticSheafPresheafEquivalence.functor n).app K
  have hcl : (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      X.affineChaoticRingedSite.O)).IsClosedUnderIsomorphisms :=
    inferInstance
  refine forall_congr' fun n ↦ ⟨fun ⟨_, hQC⟩ ↦ hcl.of_iso
      (X.affineChaoticSheafPresheafEquivalence.inverse.mapIso (hcomp n) ≪≫
        X.affineChaoticSheafPresheafEquivalence.unitIso.symm.app _) hQC,
    fun h ↦ ⟨Presheaf.isSheaf_bot _, hcl.of_iso
      ((X.affineChaoticSheafPresheafEquivalence.unitIso.app _).trans
        (X.affineChaoticSheafPresheafEquivalence.inverse.mapIso (hcomp n)).symm) h⟩⟩

open Stacks.ModulesOnACategory.QuasiCoherentCohomology in
/-- `D_QCoh(X_affine, 𝒪)` in the spelling of `qcohCohomologyProperty` is closed under
isomorphisms in `D(X_affine, 𝒪)`. -/
theorem Scheme.isClosedUnderIsomorphisms_qcohCohomologyProperty_affineChaotic :
    (qcohCohomologyProperty.{u} X.affineChaoticRingedSite).IsClosedUnderIsomorphisms :=
  ⟨fun {_ _} e hK n ↦ by
    obtain ⟨_, hQC⟩ := hK n
    exact ⟨Presheaf.isSheaf_bot _,
      (inferInstance : (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          X.affineChaoticRingedSite.O)).IsClosedUnderIsomorphisms).of_iso
        (X.affineChaoticSheafPresheafEquivalence.inverse.mapIso
          ((DerivedCategory.homologyFunctor _ n).mapIso e)) hQC⟩⟩

open Stacks.ModulesOnACategory.QuasiCoherentCohomology in
/-- **Item (4) on sheaves and on presheaves, as an exact equivalence.** On the chaotic site a
sheaf of modules is a presheaf of modules, and the induced equivalence of derived categories
(sheaves at the standard model, presheaves at the model of
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.DMod`) restricts to an exact equivalence
of the subcategories with quasi-coherent cohomology. -/
def Scheme.affineChaoticSheafToPresheaf :
    haveI := X.isWeakSerreClass_isQuasicoherentOnSite_affineChaotic
    haveI := affineChaotic_qcohCohomologyProperty_isTriangulated.{u} X
    LinearTriangulatedEquivalence ℤ
      (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.affineChaoticRingedSite.O))).FullSubcategory
      (qcohCohomologyProperty.{u} X.affineChaoticRingedSite).FullSubcategory :=
  haveI := X.isWeakSerreClass_isQuasicoherentOnSite_affineChaotic
  haveI := affineChaotic_qcohCohomologyProperty_isTriangulated.{u} X
  haveI := X.isClosedUnderIsomorphisms_qcohCohomologyProperty_affineChaotic
  linearTriangulatedEquivalenceOfCompιIso _ _
    ((Equivalence.mapDerivedCategory X.affineChaoticSheafPresheafEquivalence).congrFullSubcategory
      (funext fun K ↦ propext (X.qcohCohomologyProperty_affineChaotic_iff_standard K)))
    X.affineChaoticSheafPresheafEquivalence.functor.mapDerivedCategory
    (ObjectProperty.liftCompιIso _ _ _)

open Stacks.ModulesOnACategory.QuasiCoherentCohomology in
/-- **The comparison `(4) ≃ (3)` at the standard model of the derived categories of sheaves.**
The composite of `AlgebraicGeometry.Scheme.affineChaoticSheafToPresheaf`, read backwards, and
`AlgebraicGeometry.Scheme.affineChaoticToZariskiStandard`. -/
def Scheme.affineChaoticPresheafToZariskiStandard :
    haveI := affineChaotic_qcohCohomologyProperty_isTriangulated.{u} X
    LinearTriangulatedEquivalence ℤ
      (qcohCohomologyProperty.{u} X.affineChaoticRingedSite).FullSubcategory
      X.affineOpensQuasicoherentDerivedCategory :=
  haveI := X.isWeakSerreClass_isQuasicoherentOnSite_affineChaotic
  haveI := affineChaotic_qcohCohomologyProperty_isTriangulated.{u} X
  X.affineChaoticSheafToPresheaf.symm.trans X.affineChaoticToZariskiStandard

/-! ### The five categories and the exact equivalences -/

open Stacks.ModulesOnACategory.QuasiCoherentCohomology
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence

/-- The abelian structure on the modules over the structure sheaf of the small Zariski site of
`S`, Mathlib's `SheafOfModules.instAbelian` at the universes of that site: objects in
`Type (u + 1)`, morphisms and sections in `Type u`. -/
abbrev SmallZariski.abelianModules (B : BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : Abelian (SheafOfModules.{u} (SmallZariski.structureSheaf B S hS)) :=
  haveI : HasSheafify (SmallZariski.topology B S hS) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite.{u} _ _
  SheafOfModules.instAbelian _

/-- The quasi-coherent `𝒪_S`-modules form a weak Serre subcategory, Stacks 01LA:
`Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerreClass`, read with the
abelian structure found here on `SheafOfModules S.ringCatSheaf`. -/
theorem Scheme.isWeakSerreClass_isQuasicoherent_ringCatSheaf (S : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).IsWeakSerreClass :=
  Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerreClass S

/-- Restriction from the small Zariski site to the opens of `S`, the identification of modules of
Descent, Remark 03FG, as an equivalence of categories. -/
def SmallZariski.restrictModuleEquivalence (B : BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    SheafOfModules.{u} (SmallZariski.structureSheaf B S hS) ≌ SheafOfModules.{u} S.ringCatSheaf :=
  (SmallZariski.restrictModule B S hS).asEquivalence

/-- Restriction from the small Zariski site to the opens of `S` is additive: it is the
restriction of sheaves of modules along a continuous functor, computed objectwise on sections,
so it preserves addition of morphisms on the nose. -/
theorem SmallZariski.additive_restrictModuleEquivalence (B : BigZariskiSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    letI := SmallZariski.abelianModules B S hS
    (SmallZariski.restrictModuleEquivalence B S hS).functor.Additive :=
  let := SmallZariski.abelianModules B S hS
  ⟨rfl⟩

/-- **The derived category `D(S_Zar, 𝒪)` of modules on the small Zariski site**, at the standard
model: the small Zariski site has its objects in `Type (u + 1)`, so the locally small model of
`StacksFrontier.Homology.DerivedCategory.LocallySmall` does not apply to it. -/
abbrev SmallZariski.derivedCategoryModel (B : BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    letI := SmallZariski.abelianModules B S hS
    HasDerivedCategory.{u + 1} (SheafOfModules.{u} (SmallZariski.structureSheaf B S hS)) :=
  letI := SmallZariski.abelianModules B S hS
  HasDerivedCategory.standard _

/-- **The quasi-coherent modules on `(S_Zar, 𝒪)` form a weak Serre subcategory**: they are the
modules whose restriction to `S` is quasi-coherent
(`AlgebraicGeometry.SmallZariski.isQuasicoherentOnSite_iff_isQuasicoherent_restrictModule`),
restriction is an equivalence, and the quasi-coherent `𝒪_S`-modules form a weak Serre
subcategory by Stacks 01LA. -/
theorem SmallZariski.isWeakSerreClass_isQuasicoherentOnSite (B : BigZariskiSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    letI := SmallZariski.abelianModules B S hS
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (SmallZariski.structureSheaf B S hS)).IsWeakSerreClass :=
  let := SmallZariski.abelianModules B S hS
  have := SmallZariski.additive_restrictModuleEquivalence B S hS
  have := Scheme.isWeakSerreClass_isQuasicoherent_ringCatSheaf S
  ObjectProperty.isWeakSerreClass_of_iff (SheafOfModules.isQuasicoherent S.ringCatSheaf)
    (SmallZariski.restrictModuleEquivalence B S hS).functor
    (SmallZariski.isQuasicoherentOnSite_iff_isQuasicoherent_restrictModule B S hS)

/-- Restriction of `𝒪_X`-modules to the affine opens of `X`, as the functor of an equivalence,
is additive. -/
instance Scheme.additive_affineOpensModuleRestrictionEquivalence_functor (X : Scheme.{u}) :
    X.affineOpensModuleRestrictionEquivalence.functor.Additive :=
  inferInstanceAs X.affineOpensModuleRestriction.Additive

variable (B : BigZariskiSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

/-- **The comparison `(2) ≃ (1)`**: restriction from the small Zariski site to the opens of `X`,
the identification of modules of Descent, Remark 03FG, induces an exact equivalence
`D_QCoh(X_Zar, 𝒪) ≌ D_QCoh(𝒪_X)`, the quasi-coherent modules corresponding to each other by
`AlgebraicGeometry.SmallZariski.isQuasicoherentOnSite_iff_isQuasicoherent_restrictModule`. -/
def Scheme.smallZariskiQuasicoherentDerivedEquivalence :
    haveI := Scheme.isWeakSerreClass_isQuasicoherent_ringCatSheaf X
    letI := SmallZariski.abelianModules B X hX
    letI := SmallZariski.derivedCategoryModel B X hX
    haveI := SmallZariski.isWeakSerreClass_isQuasicoherentOnSite B X hX
    LinearTriangulatedEquivalence ℤ
      (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (SmallZariski.structureSheaf B X hX))).FullSubcategory
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).FullSubcategory :=
  haveI := Scheme.isWeakSerreClass_isQuasicoherent_ringCatSheaf X
  letI := SmallZariski.abelianModules B X hX
  letI := SmallZariski.derivedCategoryModel B X hX
  haveI := SmallZariski.additive_restrictModuleEquivalence B X hX
  haveI := SmallZariski.isWeakSerreClass_isQuasicoherentOnSite B X hX
  derivedCategoryBLinearTriangulatedEquivalence (SmallZariski.restrictModuleEquivalence B X hX)
    _ (SheafOfModules.isQuasicoherent X.ringCatSheaf)
    (SmallZariski.isQuasicoherentOnSite_iff_isQuasicoherent_restrictModule B X hX)

/-- **The comparison `(1) ≃ (3)`**: restriction to the affine opens induces an exact
equivalence `D_QCoh(𝒪_X) ≌ D_QCoh(X_{affine, Zar}, 𝒪)`. -/
def Scheme.affineZariskiQuasicoherentDerivedEquivalence :
    haveI := Scheme.isWeakSerreClass_isQuasicoherent_ringCatSheaf X
    LinearTriangulatedEquivalence ℤ
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).FullSubcategory
      X.affineOpensQuasicoherentDerivedCategory :=
  haveI := Scheme.isWeakSerreClass_isQuasicoherent_ringCatSheaf X
  derivedCategoryBLinearTriangulatedEquivalence X.affineOpensModuleRestrictionEquivalence
    (SheafOfModules.isQuasicoherent X.ringCatSheaf) _ fun M ↦
      (congrFun X.isQuasicoherent_eq_isQuasicoherentOnSite_ringCatSheaf M).to_iff.trans
        (X.isQuasicoherentOnSite_affineOpensModuleRestriction_iff M).symm

attribute [local instance] affineChaotic_qcohCohomologyProperty_isTriangulated

/-- **The comparison `(4) ≃ (3)`**: the change of topology `ε : X_{affine, Zar} ⟶ X_affine` of
Stacks 07A8, followed by the identification of sheaves and presheaves of modules on the chaotic
site. -/
def Scheme.affineChaoticQuasicoherentDerivedEquivalence :
    LinearTriangulatedEquivalence ℤ
      (qcohCohomologyProperty.{u} X.affineChaoticRingedSite).FullSubcategory
      X.affineOpensQuasicoherentDerivedCategory :=
  X.affineChaoticPresheafToZariskiStandard

/-- **The comparison `(4) ≃ (5)`**: on the chaotic affine site, whose restriction homomorphisms
are flat, `D_QCoh(X_affine, 𝒪)` and `QC(X_affine, 𝒪)` are the same subcategory of
`D(X_affine, 𝒪)` (Stacks 0GZR), so the identity is an exact equivalence. -/
def Scheme.affineChaoticQuasicoherentEquivQC :
    LinearTriangulatedEquivalence ℤ
      (qcohCohomologyProperty.{u} X.affineChaoticRingedSite).FullSubcategory
      (QC.{u} (affineChaoticBaseChangeData.{u} X)) :=
  linearTriangulatedEquivalenceOfEq
    (affineChaotic_isQC_eq_hasQuasicoherentCohomology.{u} X
      (affineChaoticBaseChangeData.{u} X)).symm

/-- The comparison `(4) ≃ (3)` lies over `Lε^*`: its functor, followed by the inclusion of
`D_QCoh(X_{affine, Zar}, 𝒪)`, is the inclusion of `D_QCoh(X_affine, 𝒪)` followed by the passage
from presheaves to sheaves of modules on the chaotic site and the derived pullback `Lε^*` along
the coarsening `ε`. -/
def Scheme.affineChaoticQuasicoherentDerivedEquivalenceFunctorCompιIso :
    X.affineChaoticQuasicoherentDerivedEquivalence.equivalence.functor ⋙
        (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O))).ι ≅
      (qcohCohomologyProperty.{u} X.affineChaoticRingedSite).ι ⋙
        X.affineChaoticSheafPresheafEquivalence.inverse.mapDerivedCategory ⋙
          X.affineCoarseningDerivedPullback :=
  Iso.refl _

/-- **Stacks 0GZZ.** Let `X` be a scheme, and let `Sch_Zar` be a big Zariski site containing it.
There are canonical exact equivalences between the following triangulated categories:

1. `D_QCoh(𝒪_X)`, the complexes of `𝒪_X`-modules on the ringed space `(X, 𝒪_X)` with
   quasi-coherent cohomology sheaves;
2. `D_QCoh(X_Zar, 𝒪)`, the same on the small Zariski site `X_Zar` of Topologies, Definition 020T
   (the open immersions `U → X` of `Sch_Zar`), with its structure sheaf `U ↦ Γ(U, 𝒪_U)` and
   quasi-coherence in the sense of Modules on Sites, Definition 03DL;
3. `D_QCoh(X_{affine, Zar}, 𝒪)`, the same on the category of affine opens of `X` with the
   Zariski topology;
4. `D_QCoh(X_affine, 𝒪)`, the same on the category of affine opens of `X` with the chaotic
   topology, where modules are presheaves of modules;
5. `QC(X_affine, 𝒪)`, the full subcategory of `D(X_affine, 𝒪)` of Cohomology on Sites,
   Definition 0GYV: the objects `K` for which `RΓ(V, K) ⊗^L_{𝒪(V)} 𝒪(U) ⟶ RΓ(U, K)` is an
   isomorphism for all `U ⟶ V`, formed with the derived base change of
   `AlgebraicGeometry.affineChaoticBaseChangeData`.

Formally: the five subcategories are triangulated subcategories of their ambient derived
categories, and there are equivalences of triangulated categories (an equivalence whose functor
commutes with the shifts and preserves distinguished triangles)
`(2) ≌ (1)`, `(1) ≌ (3)`, `(4) ≌ (3)` and `(4) ≌ (5)`, which are the canonical ones: each lies,
through the inclusions of the subcategories, over the canonical functor of the source, namely
derived restriction along the identification of modules of Descent, Remark 03FG; derived
restriction to the affine opens; the identification of presheaves with sheaves for the chaotic
topology followed by `Lε^*` for the morphism of ringed sites
`ε : (X_{affine, Zar}, 𝒪) ⟶ (X_affine, 𝒪)` of Cohomology on Sites, Lemma 07A8; and the identity
of `D(X_affine, 𝒪)`.

The derived categories of sheaves of modules are taken at the standard model
`HasDerivedCategory.standard`, the one the change of topology of Stacks 07A8 is constructed at;
those of presheaves of modules at the model of
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.DMod`. -/
@[stacks 0GZZ]
theorem Scheme.nonempty_quasicoherentDerived_linearTriangulatedEquivalences :
    letI := SmallZariski.abelianModules B X hX
    letI := SmallZariski.derivedCategoryModel B X hX
    haveI := Scheme.isWeakSerreClass_isQuasicoherent_ringCatSheaf X
    haveI := SmallZariski.isWeakSerreClass_isQuasicoherentOnSite B X hX
    haveI := SmallZariski.additive_restrictModuleEquivalence B X hX
    -- the five subcategories are triangulated
    (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).IsTriangulated ∧
    (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (SmallZariski.structureSheaf B X hX))).IsTriangulated ∧
    (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O))).IsTriangulated ∧
    (qcohCohomologyProperty.{u} X.affineChaoticRingedSite).IsTriangulated ∧
    (isQCProperty.{u} (affineChaoticBaseChangeData.{u} X)).IsTriangulated ∧
    -- `(2) ≃ (1)`, over derived restriction along Descent, Remark 03FG
    (∃ e : LinearTriangulatedEquivalence ℤ
        (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          (SmallZariski.structureSheaf B X hX))).FullSubcategory
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent X.ringCatSheaf)).FullSubcategory,
      Nonempty (e.equivalence.functor ⋙
          (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ≅
        (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          (SmallZariski.structureSheaf B X hX))).ι ⋙
          (SmallZariski.restrictModuleEquivalence B X hX).functor.mapDerivedCategory)) ∧
    -- `(1) ≃ (3)`, over derived restriction to the affine opens
    (∃ e : LinearTriangulatedEquivalence ℤ
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent X.ringCatSheaf)).FullSubcategory
        X.affineOpensQuasicoherentDerivedCategory,
      Nonempty (e.equivalence.functor ⋙
          (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O))).ι ≅
        (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ⋙
          X.affineOpensModuleRestrictionEquivalence.functor.mapDerivedCategory)) ∧
    -- `(4) ≃ (3)`, over sheafification for the chaotic topology followed by `Lε^*`
    (∃ e : LinearTriangulatedEquivalence ℤ
        (qcohCohomologyProperty.{u} X.affineChaoticRingedSite).FullSubcategory
        X.affineOpensQuasicoherentDerivedCategory,
      Nonempty (e.equivalence.functor ⋙
          (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O))).ι ≅
        (qcohCohomologyProperty.{u} X.affineChaoticRingedSite).ι ⋙
          X.affineChaoticSheafPresheafEquivalence.inverse.mapDerivedCategory ⋙
            X.affineCoarseningDerivedPullback)) ∧
    -- `(4) ≃ (5)`, over the identity of `D(X_affine, 𝒪)`
    (∃ e : LinearTriangulatedEquivalence ℤ
        (qcohCohomologyProperty.{u} X.affineChaoticRingedSite).FullSubcategory
        (QC.{u} (affineChaoticBaseChangeData.{u} X)),
      Nonempty (e.equivalence.functor ⋙ QCι.{u} (affineChaoticBaseChangeData.{u} X) ≅
        (qcohCohomologyProperty.{u} X.affineChaoticRingedSite).ι)) := by
  let := SmallZariski.abelianModules B X hX
  let := SmallZariski.derivedCategoryModel B X hX
  have := Scheme.isWeakSerreClass_isQuasicoherent_ringCatSheaf X
  have := SmallZariski.isWeakSerreClass_isQuasicoherentOnSite B X hX
  have := SmallZariski.additive_restrictModuleEquivalence B X hX
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨X.smallZariskiQuasicoherentDerivedEquivalence B hX, ⟨Iso.refl _⟩⟩,
    ⟨X.affineZariskiQuasicoherentDerivedEquivalence, ⟨Iso.refl _⟩⟩,
    ⟨X.affineChaoticQuasicoherentDerivedEquivalence,
      ⟨X.affineChaoticQuasicoherentDerivedEquivalenceFunctorCompιIso⟩⟩,
    ⟨X.affineChaoticQuasicoherentEquivQC, ⟨Iso.refl _⟩⟩⟩

end Chaotic

end AlgebraicGeometry

end
