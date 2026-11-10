module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaUnitShifts
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedSpaceModulesAbelian
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafSpelling
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasiCoherentDirectSums
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CoherentTorSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatnessAndRightExactness
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# The direct-sum step of the dévissage of [Stacks, Tag 08EU]

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes, let `E ∈ D_QCoh(𝒪_X)`
and let `(Zᵢ)` be a family of objects of `D_QCoh(𝒪_Y)` indexed by an arbitrary type of the scheme
universe.  If the projection-formula morphism of [Stacks, Tag 0B53],

`Rf_*E ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*K)`,

is invertible at each `K = Zᵢ`, then it is invertible at `K = ⨁ᵢ Zᵢ`.  This is the sentence of the
source's proof of [Stacks, Tag 08EU] reading *"the functors `Lf^*` and `⊗^𝐋` preserve direct sums
by construction and `Rf_*` commutes with direct sums (for complexes with quasi-coherent cohomology
sheaves) by [Stacks, Tag 08DZ]"*.

## Main results

* `Stacks.Cohomology.ProjectionFormulaQCohCoproducts.preservesColimitsOfShape_derivedTensor_obj`:
  **the derived tensor product of [Stacks, Tag 06YU] preserves direct sums in its second
  variable**, for an arbitrary first argument and an arbitrary index type of the ringed space's
  universe.
* `Stacks.Cohomology.ProjectionFormulaQCohCoproducts.isIso_projectionFormulaMap_sigma`: **the
  direct-sum step itself.**

## The argument

`projectionFormulaMap f E` is a natural transformation in its second variable — that is
`Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_natural_right` — between the two
functors of `K`

* `P K = Rf_*E ⊗^𝐋_{𝒪_Y} K`, and
* `Q K = Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*K)`.

A natural transformation which is invertible on each summand, between two functors that both
preserve the direct sum in question, is invertible at the direct sum: this is
`Stacks.Cohomology.ProjectionFormulaQCohCoproducts.isIso_of_isIso_app_of_isIso_sigmaComparison`,
whose proof is the square of the transformation at the coprojections.  So the content is the two
preservation statements.

*`P` preserves the direct sum* because the derived tensor product does so in its second variable.
That is proved here, in `preservesColimitsOfShape_derivedTensor_obj`: writing the fixed first
argument as the class of a K-flat complex `A`, the canonical map to the ordinary total tensor
complex is invertible for *every* second argument
(`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.toTensor_eq_comparisonLeft`), so
`Q ⋙ (A ⊗^𝐋 -)` is isomorphic to `Tot(A ⊗_{𝒪} -) ⋙ Q`; the complex-level functor preserves direct
sums because `⊗_{𝒪}` does ([Stacks, Tag 05NB]) and a total complex is assembled from coproducts
degreewise, `Q` preserves them, and `Q` is essentially surjective.

*`Q` preserves the direct sum* because it is the composite of three functors each of which does so
on the family at hand: `Lf^*` is a left adjoint, `E ⊗^𝐋_{𝒪_X} -` is the statement just proved, and
`Rf_*` commutes with direct sums of complexes with quasi-coherent cohomology by
[Stacks, Tag 08DZ], `Stacks.Duality.DerivedPushforward.isIso_sigmaComparison_of_isQuasicoherent`.
The quasi-coherence that last step consumes is that of `E ⊗^𝐋_{𝒪_X} Lf^*Zᵢ`, which is
[Stacks, Tag 08DX] part (1) applied to `E` and to `Lf^*Zᵢ`; the latter is in `D_QCoh(𝒪_X)` by
[Stacks, Tag 08DW] part (1).

## Implementation notes

*`attribute [local instance 10000] HasDerivedCategory.standard`, not a plain `local instance`.*
The import closure contains the locally small instances
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` and `SheafOfModules.hasDerivedCategory`; at
equal priority instance search picks one of those, which changes the morphism universe of the
derived category from `u + 1` to `u` and makes the statements below ill-typed against
`Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap`.  The same attribute at the same
priority is carried by
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/QuasiCoherentDirectSums.lean` and, at
priority `100000`, by
`StacksFrontier/AlgebraicGeometry/Intersection/TorFormula/CoherentTorSheaves.lean`, which is what
makes [Stacks, Tag 08DX] part (1) available here at all.

*Direct sums in `D(𝒪_Z)` at the standard model.*  The global instance
`SheafOfModules.hasColimitsOfShape_discrete_derivedCategory` is stated at the locally small model,
so it does not fire here; `Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory`
is the model-independent form and is registered as a local instance, exactly as in
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/QuasiCoherentDirectSums.lean`.

*`Stacks.DerivedQCoh.IsDQCoh` is applied with `R` explicit.*  Two occurrences of it in one
statement, over two different schemes, do not get independent universes if the first is left to
unification; the second is then elaborated at the wrong universe and the statement is rejected.

## References

* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 08DZ](https://stacks.math.columbia.edu/tag/08DZ)
* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula

universe u

namespace Stacks.Cohomology.ProjectionFormulaQCohCoproducts

/-! ### A transformation of functors at a direct sum -/

section Abstract

variable {C D : Type*} [Category C] [Category D]

/-- **A transformation of functors invertible on each summand is invertible at the direct sum**,
provided both functors preserve that direct sum.  The square of the transformation at the
coprojections identifies the value at the direct sum with the map induced between the two direct
sums of the values, which is invertible because each of its components is. -/
theorem isIso_of_isIso_app_of_isIso_sigmaComparison (F G : C ⥤ D)
    (τ : ∀ c : C, F.obj c ⟶ G.obj c)
    (hτ : ∀ {c c' : C} (g : c ⟶ c'), F.map g ≫ τ c' = τ c ≫ G.map g)
    {I : Type*} (Z : I → C) [HasCoproduct Z]
    [HasCoproduct fun i ↦ F.obj (Z i)] [HasCoproduct fun i ↦ G.obj (Z i)]
    (hF : IsIso (sigmaComparison F Z)) (hG : IsIso (sigmaComparison G Z))
    (h : ∀ i, IsIso (τ (Z i))) :
    IsIso (τ (∐ Z)) := by
  have hmap : IsIso (Limits.Sigma.map fun i ↦ τ (Z i)) := by
    refine ⟨Limits.Sigma.map fun i ↦ inv (τ (Z i)), ?_, ?_⟩ <;>
      exact Limits.Sigma.hom_ext _ _ fun i ↦ by simp
  have hsq : sigmaComparison F Z ≫ τ (∐ Z) =
      (Limits.Sigma.map fun i ↦ τ (Z i)) ≫ sigmaComparison G Z := by
    refine Limits.Sigma.hom_ext _ _ fun i ↦ ?_
    have hL : Limits.Sigma.ι (fun i ↦ F.obj (Z i)) i ≫ sigmaComparison F Z ≫ τ (∐ Z) =
        τ (Z i) ≫ G.map (Limits.Sigma.ι Z i) := by
      rw [← Category.assoc, ι_comp_sigmaComparison, hτ (Limits.Sigma.ι Z i)]
    have hR : Limits.Sigma.ι (fun i ↦ F.obj (Z i)) i ≫
        (Limits.Sigma.map fun i ↦ τ (Z i)) ≫ sigmaComparison G Z =
          τ (Z i) ≫ G.map (Limits.Sigma.ι Z i) := by
      rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc, ι_comp_sigmaComparison]
    rw [hL, hR]
  have hgoal : IsIso (sigmaComparison F Z ≫ τ (∐ Z)) := by
    rw [hsq]
    have := hmap
    have := hG
    infer_instance
  have := hF
  exact IsIso.of_isIso_comp_left (sigmaComparison F Z) (τ (∐ Z))

end Abstract

/-! ### Total complexes of a bifunctor and direct sums -/

section MapBifunctor

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [HasZeroMorphisms C] [HasZeroMorphisms D] [Preadditive E] [HasCoproducts.{0} E]
  (F : C ⥤ D ⥤ E) [F.PreservesZeroMorphisms]
  [∀ M, (F.obj M).PreservesZeroMorphisms]
  [∀ (A : CochainComplex C ℤ) (B : CochainComplex D ℤ),
    HomologicalComplex.HasMapBifunctor A B F (ComplexShape.up ℤ)]

/-- **`Tot(F(A, -))` is the double-complex functor followed by totalisation**, as an isomorphism
of functors on `Comp(D)`.  The two functors have the same values on the nose; on morphisms the
left-hand one inserts `F(𝟙 Aₚ, -)` in front, which is the identity. -/
def map₂HomologicalComplexObjIso (A : CochainComplex C ℤ) :
    (F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj A ≅
      (F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj A ⋙
        HomologicalComplex₂.totalFunctor E (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun {B _} g ↦ by
    have hid : ((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
            (ComplexShape.up ℤ)).map (𝟙 A)).app B ≫
          ((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
            (ComplexShape.up ℤ)).obj A).map g =
        ((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).obj A).map g := by
      rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
    exact (Category.comp_id _).trans
      ((congrArg (fun φ ↦ HomologicalComplex₂.total.map φ (ComplexShape.up ℤ)) hid).trans
        (Category.id_comp _).symm)

variable {J : Type*} [Category J] [HasColimitsOfShape J D] [HasColimitsOfShape J E]
  [∀ M, PreservesColimitsOfShape J (F.obj M)]

/-- **The total complex of a bifunctor preserves a colimit in the variable left free**, the other
being fixed at a complex `A`.  The double complex does, degreewise by
`CochainComplex.KFlat.preservesColimit_mapBifunctorObj`, and so does totalisation, by
`CochainComplex.KFlat.preservesColimit_totalFunctor`. -/
theorem preservesColimit_map₂HomologicalComplex_obj (A : CochainComplex C ℤ)
    (Dg : J ⥤ CochainComplex D ℤ) :
    PreservesColimit Dg
      ((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj A) := by
  have h₁ : PreservesColimit Dg
      ((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj A) :=
    CochainComplex.KFlat.preservesColimit_mapBifunctorObj Dg A F
  have h₂ : PreservesColimit (Dg ⋙ (F.mapBifunctorHomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj A)
      (HomologicalComplex₂.totalFunctor E (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)) :=
    CochainComplex.KFlat.preservesColimit_totalFunctor (ComplexShape.up ℤ) _
  have h₃ : PreservesColimit Dg
      ((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).obj A ⋙
        HomologicalComplex₂.totalFunctor E (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)) := comp_preservesColimit _ _
  exact preservesColimit_of_natIso _ (map₂HomologicalComplexObjIso F A).symm

/-- `Tot(F(A, -))` preserves `J`-colimits, the shape-level form of
`preservesColimit_map₂HomologicalComplex_obj`. -/
theorem preservesColimitsOfShape_map₂HomologicalComplex_obj (A : CochainComplex C ℤ) :
    PreservesColimitsOfShape J
      ((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj A) :=
  ⟨fun {Dg} ↦ preservesColimit_map₂HomologicalComplex_obj F A Dg⟩

end MapBifunctor

/-! ### The derived tensor product preserves direct sums in its second variable -/

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Cohomology.ProjectionFormulaPerfect.hasSheafifyOpens
  Stacks.Cohomology.ProjectionFormulaPerfect.wEqualsLocallyBijectiveOpens
attribute [local instance] Stacks.AssociatedSheaf.abelianModulesRingSheaf
attribute [local instance] Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory

/-- **`Tot(A ⊗_{𝒪_Z} -)` preserves direct sums.**  Tensoring with a fixed sheaf of modules
preserves all colimits by [Stacks, Tag 05NB], and the total complex is assembled from coproducts
degreewise. -/
theorem preservesColimitsOfShape_tensorComplex_obj (Z : RingedSpace.{u, u}) (I : Type u)
    (A : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules Z.sheaf) ℤ) :
    PreservesColimitsOfShape (Discrete I)
      ((Stacks.SheafOfModules.Tensor.tensorComplex Z.sheaf).obj A) := by
  have hcol : HasColimitsOfShape (Discrete I)
      (Stacks.DerivedTensor.RingedSite.Modules Z.sheaf) := inferInstance
  have hcop : HasCoproducts.{0} (Stacks.DerivedTensor.RingedSite.Modules Z.sheaf) :=
    fun _ ↦ inferInstance
  have hF : ∀ M : Stacks.DerivedTensor.RingedSite.Modules Z.sheaf,
      PreservesColimitsOfShape (Discrete I)
        ((Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf).obj M) := fun M ↦
    (Stacks.SheafOfModules.preservesColimits_sheafTensorObj Z.sheaf M).preservesColimitsOfShape
  exact preservesColimitsOfShape_map₂HomologicalComplex_obj
    (Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf) A

/-- **The derived tensor product of [Stacks, Tag 06YU] preserves direct sums in its second
variable.**  No hypothesis is placed on the first argument `A` and none on the index type beyond
its lying in the universe of the ringed space.

The first argument is written as the class of a K-flat complex, against which the canonical map
from the derived tensor product to the ordinary total tensor complex is invertible for every second
argument; the complex-level functor preserves direct sums by
`preservesColimitsOfShape_tensorComplex_obj`, the localization functor preserves them, and it is
essentially surjective, so the preservation descends. -/
theorem preservesColimitsOfShape_derivedTensor_obj (Z : RingedSpace.{u, u}) (I : Type u)
    (A : DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules Z.sheaf)) :
    PreservesColimitsOfShape (Discrete I)
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf).obj A) := by
  obtain ⟨A₀, p, hA₀, hp⟩ := Stacks.DerivedTensor.RingedSite.exists_kFlat_quasiIso Z.sheaf
    (DerivedCategory.Q.objPreimage A)
  have hpiso := (DerivedCategory.isIso_Q_map_iff_quasiIso
    (C := Stacks.DerivedTensor.RingedSite.Modules Z.sheaf) p).2 hp
  have e : (DerivedCategory.Q.obj A₀ :
      DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules Z.sheaf)) ≅ A :=
    @asIso _ _ _ _ (DerivedCategory.Q.map p) hpiso ≪≫ DerivedCategory.Q.objObjPreimageIso A
  refine (preservesColimitsOfShape_iff_of_natIso
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf).mapIso e)).1 ?_
  have hQ : PreservesColimitsOfShape (Discrete I)
      (DerivedCategory.Q (C := Stacks.DerivedTensor.RingedSite.Modules Z.sheaf)) :=
    Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts _ I
  have hTot : PreservesColimitsOfShape (Discrete I)
      ((Stacks.SheafOfModules.Tensor.tensorComplex Z.sheaf).obj A₀) :=
    preservesColimitsOfShape_tensorComplex_obj Z I A₀
  have hH : PreservesColimitsOfShape (Discrete I)
      ((Stacks.SheafOfModules.Tensor.tensorComplex Z.sheaf).obj A₀ ⋙
        DerivedCategory.Q) := comp_preservesColimitsOfShape _ _
  have ecomp : DerivedCategory.Q ⋙
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf).obj
          (DerivedCategory.Q.obj A₀) ≅
      (Stacks.SheafOfModules.Tensor.tensorComplex Z.sheaf).obj A₀ ⋙ DerivedCategory.Q :=
    NatIso.ofComponents
      (fun L ↦ (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
        Z.sheaf).comparisonLeft A₀ L hA₀) (fun {L L'} g ↦ by
          have h := (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
            Z.sheaf).toTensor_naturality (𝟙 A₀) g
          rw [DerivedCategory.Q.map_id A₀,
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf).map_id,
            NatTrans.id_app, Category.id_comp,
            (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
              Z.sheaf).toTensor_eq_comparisonLeft A₀ L hA₀,
            (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
              Z.sheaf).toTensor_eq_comparisonLeft A₀ L' hA₀] at h
          exact h)
  have hcomp : PreservesColimitsOfShape (Discrete I)
      (DerivedCategory.Q ⋙
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf).obj
          (DerivedCategory.Q.obj A₀)) :=
    (preservesColimitsOfShape_iff_of_natIso ecomp).2 hH
  exact preservesColimitsOfShape_discrete_of_essSurj_comp DerivedCategory.Q
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf).obj
      (DerivedCategory.Q.obj A₀)) I

/-! ### The two functors the projection-formula morphism goes between -/

-- The projection-formula development names the structure sheaf of a ringed space by
-- `structureSheafRing` and the tensor-product development by
-- `Stacks.SheafOfModules.Tensor.ringSheaf` of `AlgebraicGeometry.SheafedSpace.sheaf`; the two are
-- the same sheaf of rings by `rfl`, and the statements below mix them.  Without these attributes
-- the goals are not type-correct at `implicit` transparency and `rw [sigmaComparison_comp]`
-- reports that it cannot find a pattern the goal visibly contains; `Tensor.ringSheaf` itself is
-- semireducible, so it is listed too, and without it the composite of the derived pullback with
-- the derived tensor product has two spellings of `D(𝒪_X)` at its seam and
-- `comp_preservesColimitsOfShape` cannot find its second half.
attribute [local implicit_reducible] TopCat.Sheaf structureSheafRing
  CategoryTheory.sheafCompose AlgebraicGeometry.SheafedSpace.sheaf
  Stacks.SheafOfModules.Tensor.ringSheaf

/-- The source of the projection-formula morphism as a functor of the complex on the target:
`K ↦ Rf_*E ⊗^𝐋_{𝒪_Y} K`. -/
abbrev lhsFunctor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) :=
  (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.toRingedSpace.sheaf).obj
    ((derivedPushforward f.toLRSHom.toShHom).obj E)

/-- The target of the projection-formula morphism as a functor of the complex on the target:
`K ↦ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*K)`. -/
abbrev rhsFunctor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) :=
  (derivedPullback f.toLRSHom.toShHom ⋙
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        X.toRingedSpace.sheaf).obj E) ⋙
    derivedPushforward f.toLRSHom.toShHom

/-! ### Quasi-coherence of the family the pushforward is applied to -/

/-- **[Stacks, Tag 08DW] part (1) in the projection formula's spelling.**  Derived pullback along
an arbitrary morphism of schemes carries a complex with quasi-coherent cohomology to a complex with
quasi-coherent cohomology. -/
theorem isDQCoh_derivedPullback_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    (hK : Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing Y.toRingedSpace) K) :
    Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing X.toRingedSpace)
      ((derivedPullback f.toLRSHom.toShHom).obj K) :=
  fun i ↦ Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel f K hK i

/-- **[Stacks, Tag 08DX] part (1) in the projection formula's spelling.**  If `E` and `K` have
quasi-coherent cohomology then so does `E ⊗^𝐋_{𝒪_X} K`. -/
theorem isDQCoh_derivedTensor_obj (X : Scheme.{u})
    (E K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hE : Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing X.toRingedSpace) E)
    (hK : Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing X.toRingedSpace) K) :
    Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing X.toRingedSpace)
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        X.toRingedSpace.sheaf).obj E).obj K) :=
  fun i ↦ AlgebraicGeometry.TorFormula.isQuasicoherent_homology_derivedTensor X E K hE hK i

/-! ### The two preservation statements -/

/-- **The source of the projection-formula morphism preserves direct sums**: it is the derived
tensor product with `Rf_*E` in the free variable. -/
theorem isIso_sigmaComparison_lhsFunctor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    {I : Type u}
    (Z : I → DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))) :
    IsIso (sigmaComparison (lhsFunctor f E) Z) := by
  have hp : PreservesColimitsOfShape (Discrete I) (lhsFunctor f E) :=
    preservesColimitsOfShape_derivedTensor_obj Y.toRingedSpace I _
  exact isIso_sigmaComparison_of_preservesColimit _ _ inferInstance

/-- **The target of the projection-formula morphism preserves direct sums of complexes with
quasi-coherent cohomology.**  `Lf^*` is a left adjoint, `E ⊗^𝐋_{𝒪_X} -` preserves direct sums by
`preservesColimitsOfShape_derivedTensor_obj`, and `Rf_*` commutes with the direct sum of the
resulting family by [Stacks, Tag 08DZ], that family consisting of complexes with quasi-coherent
cohomology. -/
theorem isIso_sigmaComparison_rhsFunctor {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hE : Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing X.toRingedSpace) E)
    {I : Type u}
    (Z : I → DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    (hZ : ∀ i, Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing Y.toRingedSpace) (Z i)) :
    IsIso (sigmaComparison (rhsFunctor f E) Z) := by
  have hpa : PreservesColimitsOfSize.{u, u} (derivedPullback f.toLRSHom.toShHom) :=
    (derivedAdjunction f.toLRSHom.toShHom).leftAdjoint_preservesColimits
  have hpt : PreservesColimitsOfShape (Discrete I)
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        X.toRingedSpace.sheaf).obj E) :=
    preservesColimitsOfShape_derivedTensor_obj X.toRingedSpace I E
  have hcomp : PreservesColimitsOfShape (Discrete I)
      (derivedPullback f.toLRSHom.toShHom ⋙
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
          X.toRingedSpace.sheaf).obj E) := comp_preservesColimitsOfShape _ _
  have hfst : IsIso (sigmaComparison (derivedPullback f.toLRSHom.toShHom ⋙
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        X.toRingedSpace.sheaf).obj E) Z) :=
    isIso_sigmaComparison_of_preservesColimit _ _ inferInstance
  have hqc : ∀ (i : I) (j : ℤ), ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj
        ((derivedPullback f.toLRSHom.toShHom ⋙
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
            X.toRingedSpace.sheaf).obj E).obj (Z i))).IsQuasicoherent := fun i ↦
    isDQCoh_derivedTensor_obj X E _ hE (isDQCoh_derivedPullback_obj f (Z i) (hZ i))
  have hpush : IsIso (sigmaComparison (derivedPushforward f.toLRSHom.toShHom)
      fun i ↦ (derivedPullback f.toLRSHom.toShHom ⋙
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
          X.toRingedSpace.sheaf).obj E).obj (Z i)) :=
    Stacks.Duality.DerivedPushforward.isIso_sigmaComparison_of_isQuasicoherent f _ hqc
  have hgoal : IsIso (sigmaComparison ((derivedPullback f.toLRSHom.toShHom ⋙
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        X.toRingedSpace.sheaf).obj E) ⋙ derivedPushforward f.toLRSHom.toShHom) Z) := by
    rw [sigmaComparison_comp]
    have := hfst
    have := hpush
    infer_instance
  exact hgoal

/-! ### The direct-sum step of [Stacks, Tag 08EU] -/

/-- **The direct-sum step of the dévissage of [Stacks, Tag 08EU].**  Let `f : X ⟶ Y` be a
quasi-compact and quasi-separated morphism of schemes, `E` a complex of `𝒪_X`-modules with
quasi-coherent cohomology and `(Zᵢ)` a family of complexes of `𝒪_Y`-modules with quasi-coherent
cohomology, indexed by an arbitrary type of the scheme universe.  If the projection-formula
morphism of [Stacks, Tag 0B53] is invertible at each `Zᵢ`, then it is invertible at `⨁ᵢ Zᵢ`.

No boundedness, flatness, perfectness or affineness enters.  The morphism is natural in its second
argument by
`Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_natural_right`, and both of the
functors it goes between preserve this direct sum. -/
theorem isIso_projectionFormulaMap_sigma {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hE : Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing X.toRingedSpace) E)
    {I : Type u}
    (Z : I → DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    [HasCoproduct Z]
    (hZ : ∀ i, Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing Y.toRingedSpace) (Z i))
    (h : ∀ i, IsIso (projectionFormulaMap f.toLRSHom.toShHom E (Z i))) :
    IsIso (projectionFormulaMap f.toLRSHom.toShHom E (∐ Z)) :=
  isIso_of_isIso_app_of_isIso_sigmaComparison (lhsFunctor f E) (rhsFunctor f E)
    (fun K ↦ projectionFormulaMap f.toLRSHom.toShHom E K)
    (fun {_ _} g ↦ projectionFormulaMap_natural_right f.toLRSHom.toShHom E g) Z
    (isIso_sigmaComparison_lhsFunctor f E Z)
    (isIso_sigmaComparison_rhsFunctor f E hE Z hZ) h

end Stacks.Cohomology.ProjectionFormulaQCohCoproducts

end
