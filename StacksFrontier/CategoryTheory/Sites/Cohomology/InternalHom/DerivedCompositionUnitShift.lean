module

public import StacksFrontier.Algebra.Homology.TotalSingleRow
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionMapSourceShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomSourceTriangulated
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDualDevissage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDualRepresentatives
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.QuasiIsoInvariance
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorHomInterchangeQuasiIso
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical map of Stacks 08JD at a shift of the structure sheaf

Let `(C, O)` be a ringed site.  The base case of the dévissage of Stacks 08JJ is that the
canonical map

`Φ_L : M ⊗^L_O L^∨ ⟶ RSheafHom(L, M)`

of Stacks 08JD is invertible at `L = O`,
`AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_structureSheaf`.  This file
proves it invertible at **every shift** `O⟦b⟧` of the structure sheaf, *directly* — without the
compatibility of `Φ` with the shift, which does not follow from the fields of the derived tensor
product datum of Stacks 06YU as they stand.

That is what makes the dévissage at the Koszul complexes of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulDerivedTensorDual`
unconditional: run on the shift-closed predicate `fun A ↦ ∀ n, IsIso (Φ_{A⟦n⟧})`, that induction
needs the shifts of `Φ` **only at the structure sheaf**, which is this file.

The mechanism is that the shift is absorbed by the *source complex* rather than by `Φ`.  The
K-flat computation of `Φ` on representatives,
`AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom_kFlatModel`, reads `Φ` at the class of
a complex `E` through a K-flat complex `H` mapping to `SheafHom(E, J)`; taking `E = O[0]⟦b⟧` and
`H = O[0]⟦c⟧` with `b + c = 0`, the chain-level composition morphism that computes it is
`compositionMap X (O[0]⟦b⟧) J I`, and
`AlgebraicGeometry.RingedSite.compositionMap_sourceShift` identifies that with the shift of
`compositionMap X O[0] J I` — whose value the unit law
`AlgebraicGeometry.RingedSite.compositionMap_structureSheafSource_eq` already computes.  No sign
survives: the Koszul sign of the total-complex comparison cancels the two source-shift signs.

## Main definitions

None.

## Main results

* `Stacks.SheafOfModules.isKFlat_shift`: **a shift of a K-flat complex is K-flat.**  The closure
  property the choice `H = O[0]⟦c⟧` needs.
* `AlgebraicGeometry.RingedSite.tensorTotalShiftIso₂_hom_naturality₂`: the Koszul comparison
  `Tot(A ⊗_O Z⟦k⟧) ≅ Tot(A ⊗_O Z)⟦k⟧` is natural in the second factor.
* `AlgebraicGeometry.RingedSite.compositionMap_shiftedStructureSheafSource_eq`: **the unit law
  for composition at a shifted structure-sheaf source.**  Its right-hand side is a composite of
  isomorphisms of complexes with one quasi-isomorphism, which is the whole point.
* `AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_shiftedStructureSheaf`:
  **the canonical map of Stacks 08JD is invertible at every shift of the structure sheaf.**
* `AlgebraicGeometry.RingedSite.isTriangulated_tensorDualSourceFunctor`: the source of `Φ` is a
  triangulated functor of the dualized variable, the composite instance named.

## Implementation notes

`Stacks.SheafOfModules.isKFlat_shift` is stated here rather than beside the other closure
properties of K-flatness because `CochainComplex.KFlat.kFlat_shift` of
`StacksFrontier.Homology.KFlat.Closure` is the statement for complexes of modules over a ring, and
the sheaf-theoretic `Stacks.SheafOfModules.IsKFlat` shifts the *second* tensor variable, so the
comparison it uses is `CochainComplex.mapBifunctorShift₂Iso` rather than the `₁` one.

The universes are the diagonal `RingedSite.{u, u, u}` with the standard derived category, as in
every file of the derived internal Hom cluster.

## References

* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 0A95](https://stacks.math.columbia.edu/tag/0A95)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.SheafOfModules

/-- **A shift of a K-flat complex is K-flat.**  K-flatness of `K` is the acyclicity of
`Tot(F ⊗_O K)` for every acyclic `F`, and `Tot(F ⊗_O K⟦c⟧) ≅ Tot(F ⊗_O K)⟦c⟧` by the Koszul
comparison of Stacks 0FNG, so this is the stability of acyclicity under the shift. -/
theorem isKFlat_shift {C₀ : Type u} [SmallCategory C₀] {J₀ : GrothendieckTopology C₀}
    (S : Sheaf J₀ CommRingCat.{u})
    [HasWeakSheafify J₀ AddCommGrpCat.{u}] [J₀.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasBinaryBiproducts (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S))]
    [(Stacks.SheafOfModules.Tensor.sheafTensor S).Additive]
    [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor S).obj A).Additive]
    [∀ (K₁ K₂ : HomologicalComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S)) (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ (Stacks.SheafOfModules.Tensor.sheafTensor S) (ComplexShape.up ℤ)]
    {K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S)) ℤ}
    (hK : IsKFlat S K) (c : ℤ) :
    IsKFlat S (K⟦c⟧) := fun F hF i =>
  HomologicalComplex.ExactAt.of_iso
    (StacksDraft.TotalSingleRow.acyclic_shiftFunctor_obj (hK F hF) c i)
    (CochainComplex.mapBifunctorShift₂Iso F K
      (Stacks.SheafOfModules.Tensor.sheafTensor S) c).symm

end Stacks.SheafOfModules

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})

section Chain

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms
  curriedTensorAdditive curriedTensorObjAdditive

/-- **The Koszul comparison of the total tensor complex is natural in its second factor.**  Both
sides are pinned on the homogeneous local pure tensors, where the comparison multiplies the
`(t, r)` summand by `(-1)^(t k)` and the induced map acts on the two factors separately, so the
sign is paid on both sides of the square. -/
lemma tensorTotalShiftIso₂_hom_naturality₂
    (A Z Z' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (v : Z ⟶ Z') (k : ℤ) :
    tensorTotalMap X (𝟙 A) ((CategoryTheory.shiftFunctor _ k).map v) ≫
        (tensorTotalShiftIso₂ X A Z' k).hom =
      (tensorTotalShiftIso₂ X A Z k).hom ≫
        (CategoryTheory.shiftFunctor _ k).map (tensorTotalMap X (𝟙 A) v) := by
  refine tensorTotal_hom_ext X fun U t r a b => ?_
  rw [HomologicalComplex.comp_f, comp_val_app_apply', tensorTotalMap_tensorTotalSection,
    tensorTotalShiftIso₂_tensorTotalSection, HomologicalComplex.comp_f, comp_val_app_apply',
    tensorTotalShiftIso₂_tensorTotalSection, val_app_unitsSmul]
  simp only [CochainComplex.shiftFunctor_map_f']
  rw [tensorTotalMap_tensorTotalSectionAt X (𝟙 A) v U t (r + k) (t + r + k) (by omega) a b]

end Chain

section Derived

open Pretriangulated Pretriangulated.Opposite

attribute [local instance] HasDerivedCategory.standard

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  (T : Stacks.SheafOfModules.DerivedTensorProduct X)

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
        (ComplexShape.up ℤ)),
      HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
        (ComplexShape.up ℤ)] in
/-- **The unit law for the chain-level composition morphism at a shifted structure-sheaf
source.**  For K-injective complexes `J`, `I`, a morphism `g : O[0] ⟶ J` and `b + c = 0`, the
composition morphism at source `O[0]⟦b⟧`, precomposed in its right tensor factor with the shift
of the section of `SheafHom(O[0], J)` named by `g` followed by the source-shift identification,
is the Koszul comparison, the shift of the collapse of the total tensor product against the
structure sheaf followed by precomposition with `g`, and the source-shift identification.

Every factor on the right is an isomorphism of complexes except `SheafHom(g, I)`, which is a
quasi-isomorphism by Stacks 0A95; that is what makes the whole invertible in the derived
category.

The sign bookkeeping is `AlgebraicGeometry.RingedSite.compositionMap_sourceShift`: the Koszul
sign of `tensorTotalShiftIso₂` cancels the discrepancy between the two source-shift signs. -/
theorem compositionMap_shiftedStructureSheafSource_eq
    (J I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (g : structureSheafComplex X ⟶ J) (b c : ℤ) (hc : b + c = 0) :
    tensorTotalMap X (𝟙 (sheafHomComplex X J I).obj)
          ((CategoryTheory.shiftFunctor _ c).map (g ≫ (structureSheafHomIso X J).inv) ≫
            (sheafHomSourceShiftIso' X (K := structureSheafComplex X) (M := J) b c hc).hom) ≫
        compositionMap X (structureSheafComplex X⟦b⟧) J I =
      (tensorTotalShiftIso₂ X (sheafHomComplex X J I).obj (structureSheafComplex X) c).hom ≫
        (CategoryTheory.shiftFunctor _ c).map
            (tensorTotalStructureSheafCollapse X (sheafHomComplex X J I).obj ≫
              homMap X g (𝟙 I)) ≫
          (sheafHomSourceShiftIso' X (K := structureSheafComplex X) (M := I) b c hc).hom := by
  have hsplit : tensorTotalMap X (𝟙 (sheafHomComplex X J I).obj)
        ((CategoryTheory.shiftFunctor _ c).map (g ≫ (structureSheafHomIso X J).inv) ≫
          (sheafHomSourceShiftIso' X (K := structureSheafComplex X) (M := J) b c hc).hom) =
      tensorTotalMap X (𝟙 (sheafHomComplex X J I).obj)
          ((CategoryTheory.shiftFunctor _ c).map (g ≫ (structureSheafHomIso X J).inv)) ≫
        tensorTotalMap X (𝟙 (sheafHomComplex X J I).obj)
          (sheafHomSourceShiftIso' X (K := structureSheafComplex X) (M := J) b c hc).hom := by
    rw [tensorTotalMap_comp, Category.comp_id]
  rw [hsplit, Category.assoc,
    compositionMap_sourceShift X (structureSheafComplex X) J I b c hc,
    ← Category.assoc, ← Category.assoc,
    tensorTotalShiftIso₂_hom_naturality₂ X (sheafHomComplex X J I).obj (structureSheafComplex X)
      (sheafHomComplex X (structureSheafComplex X) J).obj
      (g ≫ (structureSheafHomIso X J).inv) c,
    Category.assoc, Category.assoc, ← CategoryTheory.Functor.map_comp_assoc,
    compositionMap_structureSheafSource_eq X g]

/-- The image in the derived category of the shift of a quasi-isomorphism is invertible. -/
private theorem isIso_Q_map_shiftFunctor_map {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {K L : CochainComplex C ℤ} (φ : K ⟶ L) [QuasiIso φ] (c : ℤ) :
    IsIso (DerivedCategory.Q.map ((CategoryTheory.shiftFunctor _ c).map φ)) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 ((CochainComplex.quasiIso_shift_iff φ c).2 ‹_›)

variable (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- **The source of the canonical map of Stacks 08JD is a triangulated functor of the dualized
variable.**  It is the composite of the derived dual — triangulated by
`AlgebraicGeometry.RingedSite.derivedSheafHomFlipIsTriangulated` — with the derived tensor
product in its right variable, triangulated by the `exact_right` field of Stacks 06YU, so
Mathlib's instance for a composite of triangulated functors applies.  It is spelled out because
instance search does not assemble it unaided: the two factors have to be named first. -/
instance isTriangulated_tensorDualSourceFunctor :
    (tensorDualSourceFunctor X T M).IsTriangulated := by
  let : ((derivedSheafHomBifunctor X).flip.obj (derivedStructureSheaf X)).IsTriangulated :=
    derivedSheafHomFlipIsTriangulated X (derivedStructureSheaf X)
  let : (T.tensor.obj M).IsTriangulated := T.exact_right M
  exact (inferInstance : (((derivedSheafHomBifunctor X).flip.obj (derivedStructureSheaf X) ⋙
    T.tensor.obj M).IsTriangulated))

/-- **The canonical map of Stacks 08JD is invertible at every shift of the structure sheaf.**
For every integer `b` and every object `M` of `D(O)` the map

`Φ : M ⊗^L_O (O⟦b⟧)^∨ ⟶ RSheafHom(O⟦b⟧, M)`

is an isomorphism.  At `b = 0` this is the base case
`AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_structureSheaf`; the content for
general `b` is that the shift can be absorbed by the source complex, by
`compositionMap_shiftedStructureSheafSource_eq`, and so needs no compatibility of `Φ` itself with
the shift.

This is the only place where the dévissage of Stacks 08JJ at the Koszul complexes needs a shift,
which is why that dévissage does not need
`CategoryTheory.NatTrans.CommShift (derivedTensorDualNatTrans X T M) ℤ`. -/
theorem isIso_derivedTensorDualToSheafHom_shiftedStructureSheaf (b : ℤ) :
    IsIso (derivedTensorDualToSheafHom X T (derivedStructureSheaf X⟦b⟧) M) := by
  set c : ℤ := -b with hcdef
  have hc : b + c = 0 := by omega
  -- the K-injective resolution `g` of the structure sheaf, and the K-injective model of `M`
  set J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
    kInjectiveModel X (derivedStructureSheaf X) with hJ
  set I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
    kInjectiveModel X M with hI
  obtain ⟨g, hgeq⟩ := exists_Q_map_eq_of_isKInjective X (A := structureSheafComplex X) (I := J)
    (kInjectiveModelIso X (derivedStructureSheaf X)).inv
  have hgiso : IsIso (DerivedCategory.Q.map g) := by rw [hgeq]; infer_instance
  have hgq : QuasiIso g := (DerivedCategory.isIso_Q_map_iff_quasiIso _ g).mp hgiso
  -- the K-flat complex `H` and the morphism `f` the K-flat computation of `Φ` is read through
  set u : structureSheafComplex X ⟶ (sheafHomComplex X (structureSheafComplex X) J).obj :=
    g ≫ (structureSheafHomIso X J).inv with hu
  have huq : QuasiIso u := by
    have : IsIso (structureSheafHomIso X J).inv := (structureSheafHomIso X J).isIso_inv
    exact (inferInstance : QuasiIso (g ≫ (structureSheafHomIso X J).inv))
  set f : structureSheafComplex X⟦c⟧ ⟶
      (sheafHomComplex X (structureSheafComplex X⟦b⟧) J).obj :=
    (CategoryTheory.shiftFunctor _ c).map u ≫
      (sheafHomSourceShiftIso' X (K := structureSheafComplex X) (M := J) b c hc).hom with hf
  have hfiso : IsIso (DerivedCategory.Q.map f) := by
    have := isIso_Q_map_shiftFunctor_map u c
    rw [hf, Functor.map_comp]
    infer_instance
  have hH : Stacks.SheafOfModules.IsKFlat X.O (structureSheafComplex X⟦c⟧) :=
    Stacks.SheafOfModules.isKFlat_shift X.O (Stacks.SheafOfModules.isKFlat_single_unit X.O) c
  -- the right-hand side of the K-flat computation is invertible in `D(O)`
  have hrhs : IsIso (DerivedCategory.Q.map
      (tensorTotalMap X (𝟙 (sheafHomComplex X J I).obj) f ≫
        compositionMap X (structureSheafComplex X⟦b⟧) J I)) := by
    rw [hf, compositionMap_shiftedStructureSheafSource_eq X J I g b c hc]
    have hcol : IsIso (tensorTotalStructureSheafCollapse X (sheafHomComplex X J I).obj) :=
      (tensorTotalUnitIso X (sheafHomComplex X J I).obj).isIso_inv
    have : QuasiIso (homMap X g (𝟙 I)) := homMap_quasiIso X (𝟙 I) g
    have := isIso_Q_map_shiftFunctor_map
      (tensorTotalStructureSheafCollapse X (sheafHomComplex X J I).obj ≫ homMap X g (𝟙 I)) c
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    infer_instance
  -- the source comparison of the K-flat computation is invertible
  have hsrc : IsIso (derivedTensorDualSourceComparison X T (structureSheafComplex X⟦b⟧) J I
      (structureSheafComplex X⟦c⟧) g f) := by
    dsimp only [derivedTensorDualSourceComparison, derivedTensorMap]
    have ha : IsIso (((derivedInternalHomOfBifunctor X).hom.map
        (DerivedCategory.Q.map g).op).app (DerivedCategory.Q.obj I) ≫
      (derivedStructureSheafHomIso X (DerivedCategory.Q.obj I)).hom) := by infer_instance
    have hb : IsIso (DerivedCategory.Q.map f ≫
        ((derivedInternalHomOfBifunctor X).homComparison (structureSheafComplex X⟦b⟧) J).inv ≫
        ((derivedInternalHomOfBifunctor X).hom.obj
          (op (DerivedCategory.Q.obj (structureSheafComplex X⟦b⟧)))).map
            (inv (DerivedCategory.Q.map g))) := by infer_instance
    have : IsIso (T.tensor.map (((derivedInternalHomOfBifunctor X).hom.map
        (DerivedCategory.Q.map g).op).app (DerivedCategory.Q.obj I) ≫
      (derivedStructureSheafHomIso X (DerivedCategory.Q.obj I)).hom)) :=
      Functor.map_isIso _ _
    infer_instance
  -- so `Φ` is invertible at `Q (O[0]⟦b⟧)` with target `Q I`
  have key := derivedTensorDualToSheafHom_kFlatModel X T (structureSheafComplex X⟦b⟧) J I
    (structureSheafComplex X⟦c⟧) g f hH
  have hall : IsIso (derivedTensorDualSourceComparison X T (structureSheafComplex X⟦b⟧) J I
        (structureSheafComplex X⟦c⟧) g f ≫
      derivedTensorDualToSheafHom X T
          (DerivedCategory.Q.obj (structureSheafComplex X⟦b⟧)) (DerivedCategory.Q.obj I) ≫
        ((derivedInternalHomOfBifunctor X).homComparison (structureSheafComplex X⟦b⟧) I).hom) := by
    rw [key, ← CategoryTheory.Functor.map_comp]
    infer_instance
  rw [isIso_comp_left_iff, isIso_comp_right_iff] at hall
  -- transport the target along the K-injective model and the source along the shift of `Q`
  refine isIso_derivedTensorDualToSheafHom_of_iso X T
    ((DerivedCategory.Q.commShiftIso b).app (structureSheafComplex X)).symm M ?_
  exact isIso_derivedTensorDualToSheafHom_of_iso_target X T _
    (kInjectiveModelIso X M).symm hall

end Derived

end AlgebraicGeometry.RingedSite

end
