module

public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.DualizingInvertible
public import StacksFrontier.AlgebraicGeometry.Modules.DerivedMonoidalInstanceIndependence
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.Homology.DerivedCategory.GrothendieckModelTargetIso
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestrictionNaturality

/-!
# Invertibility in `D(𝒪_X)` is local on `X`

Let `X` be a scheme and `E` an object of `D(𝒪_X)`. If every point of `X` has an open
neighbourhood `W` such that the restriction `E|_W` is an invertible object of `D(𝒪_W)`, then `E`
is an invertible object of `D(𝒪_X)`. This is the globalization used by [Stacks, Tag 0C08] and
[Stacks, Tag 0FYX]: invertibility of an object is an existence statement about objects, hence not
local by itself, but it is equivalent to invertibility of the evaluation morphism, which is local
(`Stacks.Cohomology.SliceDerivedSheafHom.isInvertible_of_isInvertible_restriction`).

## Main results

* `Stacks.Duality.isInvertible_restrictD_of_isInvertible_restrictFunctor` — invertibility on the
  open subscheme `W` gives invertibility on the slice site over `W`, at the standard model.
* `Stacks.Duality.isInvertible_of_forall_exists_isInvertible_restrictFunctor` — the
  globalization, at an arbitrary one of the two models.

## Implementation notes

The open subscheme `W` and the slice site `Opens(X)/W` are identified by
`AlgebraicGeometry.Scheme.Modules.overEquiv`, and restriction to the open subscheme is the
restriction to the slice site followed by that equivalence
(`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`). The glueing lemma is stated at the
standard model; invertibility of an object of `D(𝒪_X)` does not depend on the model
(`AlgebraicGeometry.Scheme.Modules.isInvertible_standard_iff`).
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace

universe u

namespace Stacks.Duality

section Standard

variable {X : Scheme.{u}}

/-- **Invertibility on an open subscheme is invertibility on the slice site.** If `E|_W` is an
invertible object of `D(𝒪_W)`, then the restriction of `E` to the slice site `Opens(X)/W` is
invertible, for the derived tensor product of that ringed site; the derived categories are the
standard ones. -/
theorem isInvertible_restrictD_of_isInvertible_restrictFunctor (W : X.Opens)
    (E : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _))
    (h : letI : ∀ (C : Type (u + 1)) [Category.{u} C] [Abelian C], HasDerivedCategory.{u + 1} C :=
        fun C _ _ => HasDerivedCategory.standard C
      letI := Scheme.Modules.derivedMonoidal W.toScheme
      MonoidalCategory.IsInvertible
        ((Scheme.Modules.restrictFunctor W.ι).mapDerivedCategory.obj E)) :
    letI := RingedSite.derivedTensorMonoidal
      ((Stacks.SheafOfModules.ringedSite X.sheaf).over W)
    MonoidalCategory.IsInvertible
      ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD
        (Stacks.SheafOfModules.ringedSite X.sheaf) W).obj E) := by
  let : ∀ (C : Type (u + 1)) [Category.{u} C] [Abelian C], HasDerivedCategory.{u + 1} C :=
    fun C _ _ => HasDerivedCategory.standard C
  have : HasSheafify ((Opens.grothendieckTopology X).over W) AddCommGrpCat.{u} := inferInstance
  have : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} := inferInstance
  let e : (Scheme.Modules.overEquiv W).functor.mapDerivedCategory.obj
      ((SheafOfModules.overFunctor.{u} X.ringCatSheaf W).mapDerivedCategory.obj E) ≅
      (Scheme.Modules.restrictFunctor W.ι).mapDerivedCategory.obj E :=
    ((Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso
        (SheafOfModules.overFunctor.{u} X.ringCatSheaf W)
        (Scheme.Modules.overEquiv W).functor).symm ≪≫
      Stacks.Homology.mapDerivedCategoryIsoOfIso
        (SheafOfModules.overFunctor.{u} X.ringCatSheaf W ⋙ (Scheme.Modules.overEquiv W).functor)
        (Scheme.Modules.restrictFunctor W.ι)
        (instGa := Scheme.Modules.restrictFunctor_additive W.ι)
        (instGl := Scheme.Modules.restrictFunctor_preservesFiniteLimits W.ι)
        (instGc := preservesFiniteColimits_of_natIso (Scheme.Modules.overFunctorEquiv W))
        (Scheme.Modules.overFunctorEquiv W)).app E
  have h3 := @MonoidalCategory.isInvertible_of_iso _ _
    (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal
      (Stacks.SheafOfModules.OverEquivTensor.openRingSheaf X W)) _ _ e.symm h
  have h4 := Stacks.SheafOfModules.OverEquivTensor.isInvertible_of_isInvertible_overEquiv X W _ h3
  exact @MonoidalCategory.isInvertible_of_tensorComparison_of_braided _ _
      (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal
        (Stacks.SheafOfModules.OverEquivTensor.sliceRingSheaf X W)) _ _
      (RingedSite.derivedTensorMonoidal ((Stacks.SheafOfModules.ringedSite X.sheaf).over W))
      (RingedSite.derivedTensorSymmetric
        ((Stacks.SheafOfModules.ringedSite X.sheaf).over W)).toBraidedCategory
      (𝟭 _)
      (fun A B => ((Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso
        (Stacks.SheafOfModules.OverEquivTensor.sliceRingSheaf X W)
        (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct.{u, u + 1}
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct
            ((Stacks.SheafOfModules.ringedSite X.sheaf).over W)))).app A).app B)
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso
        (Stacks.SheafOfModules.OverEquivTensor.sliceRingSheaf X W)) _ h4

/-- **Invertibility in `D(𝒪_X)` is local, at the standard model.** -/
theorem isInvertible_of_forall_exists_isInvertible_restrictFunctor_standard
    (E : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _))
    (h : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧
      letI : ∀ (C : Type (u + 1)) [Category.{u} C] [Abelian C], HasDerivedCategory.{u + 1} C :=
        fun C _ _ => HasDerivedCategory.standard C
      letI := Scheme.Modules.derivedMonoidal W.toScheme
      MonoidalCategory.IsInvertible
        ((Scheme.Modules.restrictFunctor W.ι).mapDerivedCategory.obj E)) :
    letI := HasDerivedCategory.standard X.Modules
    letI := Scheme.Modules.derivedMonoidal X
    MonoidalCategory.IsInvertible E := by
  let : ∀ (C : Type (u + 1)) [Category.{u} C] [Abelian C], HasDerivedCategory.{u + 1} C :=
    fun C _ _ => HasDerivedCategory.standard C
  choose W hxW hW using h
  have hY : (Stacks.SheafOfModules.ringedSite X.sheaf).J.CoversTop W :=
    (Opens.coversTop_iff _ _).2 (TopologicalSpace.IsOpenCover.mk (eq_top_iff.2 fun x _ =>
      Opens.mem_iSup.2 ⟨x, hxW x⟩))
  have h' := Stacks.Cohomology.SliceDerivedSheafHom.isInvertible_of_isInvertible_restriction
    (Stacks.SheafOfModules.ringedSite X.sheaf) hY E
    (fun x => isInvertible_restrictD_of_isInvertible_restrictFunctor (W x) E (hW x))
  exact @MonoidalCategory.isInvertible_of_tensorComparison_of_braided _ _
      (RingedSite.derivedTensorMonoidal (Stacks.SheafOfModules.ringedSite X.sheaf)) _ _
      (Scheme.Modules.derivedMonoidal X) (Scheme.Modules.derivedSymmetric X).toBraidedCategory
      (𝟭 _)
      (fun A B => (((Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso X.sheaf
        (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct.{u, u + 1}
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct
            (Stacks.SheafOfModules.ringedSite X.sheaf)))).app A).app B).symm)
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso X.sheaf).symm E h'

end Standard

variable {X : Scheme.{u}}

/-- **Invertibility in `D(𝒪_X)` is local on `X`**, at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`: if every point of `X` has an open
neighbourhood `W` on which `E|_W` is an invertible object of `D(𝒪_W)`, then `E` is an invertible
object of `D(𝒪_X)`. -/
theorem isInvertible_of_forall_exists_isInvertible_restrictFunctor
    (E : DerivedCategory X.Modules)
    (h : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧
      letI := Scheme.Modules.derivedMonoidal W.toScheme
      MonoidalCategory.IsInvertible
        ((Scheme.Modules.restrictFunctor W.ι).mapDerivedCategory.obj E)) :
    letI := Scheme.Modules.derivedMonoidal X
    MonoidalCategory.IsInvertible E := by
  refine (Scheme.Modules.isInvertible_standard_iff X E).1
    (isInvertible_of_forall_exists_isInvertible_restrictFunctor_standard E fun x => ?_)
  obtain ⟨W, hxW, hW⟩ := h x
  refine ⟨W, hxW, ?_⟩
  let Φ := StacksDraft.DerivedModel.schemeModulesComparison W.toScheme
  let Mstd := @Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _) _ _ _
    (HasDerivedCategory.standard _) (Scheme.Modules.restrictFunctor W.ι) _ _ _ |>.obj E
  let c : Φ.functor.obj Mstd ≅ Φ.functor.obj
      ((Scheme.Modules.restrictFunctor W.ι).mapDerivedCategory.obj E) :=
    (Stacks.Injectives.mapDerivedCategoryTargetModelIso W.toScheme.Modules
        (hd₁ := HasDerivedCategory.standard _) (Scheme.Modules.restrictFunctor W.ι)).app E ≪≫
      Stacks.Injectives.mapDerivedCategoryObjIso X.Modules
        (Scheme.Modules.restrictFunctor W.ι) E
  exact @MonoidalCategory.isInvertible_of_iso _ _
    (@Scheme.Modules.derivedMonoidal W.toScheme (HasDerivedCategory.standard _)) _ _
    (Φ.functor.preimageIso c).symm ((Scheme.Modules.isInvertible_standard_iff W.toScheme _).2 hW)

end Stacks.Duality

end
