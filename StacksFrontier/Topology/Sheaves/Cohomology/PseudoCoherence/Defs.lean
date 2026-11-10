module

public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.LocalNullHomotopy
public import StacksFrontier.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.Topology.Sheaves.Module
import StacksCore.Tactic.EgaSgaAttribute

import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StrictlyPerfectCone

/-!
# Pseudo-coherence of complexes of modules on a ringed space

A complex of `O_X`-modules is `m`-pseudo-coherent when every point has a neighbourhood over
which the complex receives a map from a strictly perfect complex which is an isomorphism on
cohomology above degree `m` and surjective in degree `m`.

## Main definitions

* `AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules` and
  `AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplex`: restriction of module sheaves
  and of complexes of module sheaves to an open subspace of a ringed space.
* `AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherentComplexFrom`,
  `AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherentComplex`,
  `AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherentFrom` and
  `AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent`: `m`-pseudo-coherence and
  pseudo-coherence of complexes and of objects of the derived category.
* `AlgebraicGeometry.RingedSpace.PseudoCoherence.sheafOfModulesEquivRestrict`: modules over the
  slice sheaf of rings on `Over U` are modules on the restricted ringed space.

## Main results

* `Stacks.PseudoCoherence.DerivedCharacterization.exists_local_lift_homotopy`: a map out of a
  strictly perfect complex lifts locally, up to homotopy, through a map which is cohomologically
  an isomorphism above the first possibly nonzero degree of the source and surjective in that
  degree.
* `Stacks.PseudoCoherence.DerivedCharacterization.exists_local_chain_map`: a morphism in the
  derived category out of a strictly perfect complex is, locally, realised by a morphism of
  complexes with the same behaviour on cohomology.

## References

* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Tag 08CC](https://stacks.math.columbia.edu/tag/08CC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace.PseudoCoherence

universe u v d

variable {X : RingedSpace.{u, u}}

/-- Restriction of module sheaves to an open subspace of a ringed space. -/
@[implicit_reducible]
def restrictModules (X : RingedSpace.{u, v}) (U : Opens X.carrier) :
    OXMod.{u, v} X ⥤ OXMod.{u, v} (X.restrict U.isOpenEmbedding) :=
  letI : (U.isOpenEmbedding.functor).IsContinuous
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
      (Opens.grothendieckTopology X.carrier) :=
    U.isOpenEmbedding.functor_isContinuous
  SheafOfModules.pushforward (F := U.isOpenEmbedding.functor)
    (𝟙 (structureSheafOfRings (X.restrict U.isOpenEmbedding)))

/-- Restriction of module sheaves to an open subspace preserves zero morphisms. -/
instance (X : RingedSpace.{u, v}) (U : Opens X.carrier) :
    (restrictModules.{u, v} X U).PreservesZeroMorphisms where
  map_zero _ _ := by
    ext
    rfl

/-- Restrict a complex of modules to the open ringed subspace `U`. -/
@[implicit_reducible]
def restrictComplex (E : CochainComplex (OXMod.{u, u} X) ℤ) (U : Opens X.carrier) :
    CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ :=
  ((restrictModules.{u, u} X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj E

/-- A complex is `m`-pseudo-coherent if every point has a neighbourhood on which
it admits a strictly perfect approximation in degrees at least `m`. -/
abbrev IsPseudoCoherentComplexFrom (E : CochainComplex (OXMod.{u, u} X) ℤ) (m : ℤ) : Prop :=
  ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
    ∃ P : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ,
      IsStrictlyPerfect P ∧
      ∃ α : P ⟶ restrictComplex E U,
        (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
        Epi (HomologicalComplex.homologyMap α m)

/-- A complex is pseudo-coherent if it is `m`-pseudo-coherent for every integer `m`. -/
abbrev IsPseudoCoherentComplex (E : CochainComplex (OXMod.{u, u} X) ℤ) : Prop :=
  ∀ m : ℤ, IsPseudoCoherentComplexFrom E m

/-- An object of the derived category is `m`-pseudo-coherent if it has an
`m`-pseudo-coherent complex representative. -/
abbrev IsPseudoCoherentFrom [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    (E : DerivedCategory (OXMod.{u, u} X)) (m : ℤ) : Prop :=
  ∃ K : CochainComplex (OXMod.{u, u} X) ℤ,
    IsPseudoCoherentComplexFrom K m ∧ Nonempty (DerivedCategory.Q.obj K ≅ E)

/-- An object of the derived category is pseudo-coherent if it has a
pseudo-coherent complex representative. -/
abbrev IsPseudoCoherent [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    (E : DerivedCategory (OXMod.{u, u} X)) : Prop :=
  ∃ K : CochainComplex (OXMod.{u, u} X) ℤ,
    IsPseudoCoherentComplex K ∧ Nonempty (DerivedCategory.Q.obj K ≅ E)

/-- Modules over the slice sheaf of rings `(structureSheafOfRings X).over U` are equivalent to
modules on the restricted ringed space `X.restrict U.isOpenEmbedding`. -/
def sheafOfModulesEquivRestrict (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    SheafOfModules.{u} ((structureSheafOfRings X).over U) ≌
      OXMod.{u, u} (X.restrict U.isOpenEmbedding) :=
  Opens.sheafOfModulesEquivOver U (structureSheafOfRings X)

end AlgebraicGeometry.RingedSpace.PseudoCoherence

namespace Stacks.PseudoCoherence.DerivedCharacterization

universe u v₁ v₂ u₁ u₂ d

open _root_.SheafOfModules

variable {X : RingedSpace.{u, u}}
variable {E F G : CochainComplex (OXMod.{u, u} X) ℤ}

/-- A map from a strictly perfect complex lifts locally up to homotopy through a map that is
cohomologically an isomorphism above the lower bound and surjective at the lower bound. -/
@[stacks 08C8, sga "6 I 4.2" "ringed space case", sga "6 I 4.1" "special case"]
theorem exists_local_lift_homotopy (α : E ⟶ F) (f : G ⟶ F) (a : ℤ)
    (hE : IsStrictlyPerfect E) (hEa : ∀ j : ℤ, j < a → IsZero (E.X j))
    (hf_gt : ∀ j : ℤ, a < j → IsIso (HomologicalComplex.homologyMap f j))
    (hf_a : Epi (HomologicalComplex.homologyMap f a)) :
    ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ β : ((overFunctor.{u} (structureSheafOfRings X) U).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj E ⟶
          ((overFunctor.{u} (structureSheafOfRings X) U).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj G,
        Nonempty (Homotopy
          (β ≫ ((overFunctor.{u} (structureSheafOfRings X) U).mapHomologicalComplex
            (ComplexShape.up ℤ)).map f)
          (((overFunctor.{u} (structureSheafOfRings X) U).mapHomologicalComplex
            (ComplexShape.up ℤ)).map α)) := by
  have hcone := AlgebraicGeometry.RingedSpace.isZero_homology_mappingCone f a hf_gt hf_a
  intro x
  obtain ⟨U, hx, hzero⟩ :=
    Stacks.Cohomology.LocalNullHomotopy.exists_local_homotopy_zero_of_isZero_homology
    (α := α ≫ CochainComplex.mappingCone.inr f) a hE hEa hcone x
  let COpen := SheafOfModules.{u} ((structureSheafOfRings X).over U)
  let : HasFiniteBiproducts COpen := HasFiniteBiproducts.of_hasFiniteProducts
  let : HasBinaryBiproducts COpen := hasBinaryBiproducts_of_finite_biproducts _
  let R := overFunctor.{u} (structureSheafOfRings X) U
  let : R.Additive := ⟨by
    intro A B φ ψ
    ext V
    rfl⟩
  let RHC := R.mapHomologicalComplex (ComplexShape.up ℤ)
  let fOpen := RHC.map f
  let αOpen := RHC.map α
  let ιOpen := CochainComplex.mappingCone.inr fOpen
  let coneIso := CochainComplex.mappingCone.mapHomologicalComplexIso f R
  let Qh := HomotopyCategory.quotient COpen (ComplexShape.up ℤ)
  have hnull : Qh.map (RHC.map α ≫ RHC.map (CochainComplex.mappingCone.inr f)) = 0 := by
    rw [← Functor.map_comp]
    exact (HomotopyCategory.quotient_map_eq_zero_iff _).2 hzero
  have hconeInr : RHC.map (CochainComplex.mappingCone.inr f) ≫ coneIso.hom = ιOpen :=
    CochainComplex.mappingCone.map_inr (H := R) (φ := f)
  have hchain : αOpen ≫ ιOpen =
      (RHC.map α ≫ RHC.map (CochainComplex.mappingCone.inr f)) ≫ coneIso.hom := by
    dsimp only [αOpen]
    rw [← hconeInr, Category.assoc]
  have hcomp : Qh.map αOpen ≫ Qh.map ιOpen = 0 := by
    rw [← Functor.map_comp, hchain, Functor.map_comp, hnull, zero_comp]
  obtain ⟨βq, hβq⟩ := Pretriangulated.Triangle.coyoneda_exact₂ _
    (HomotopyCategory.mappingCone_triangleh_distinguished fOpen) (Qh.map αOpen) hcomp
  obtain ⟨β, hβ⟩ := Qh.map_surjective βq
  change RHC.obj E ⟶ RHC.obj G at β
  have hdiff : Qh.map (β ≫ fOpen - αOpen) = 0 := by
    rw [Functor.map_sub, Functor.map_comp]
    exact sub_eq_zero.mpr ((congrArg (· ≫ Qh.map fOpen) hβ).trans hβq.symm)
  obtain ⟨H⟩ := (HomotopyCategory.quotient_map_eq_zero_iff _).1 hdiff
  exact ⟨U, hx, β, ⟨Homotopy.equivSubZero.symm H⟩⟩

/-- An exact functor commutes with the homology of complexes: the degree-`i` homology of the image
of a complex is the image of its degree-`i` homology. -/
def mapHomologicalComplexHomologyIso {A : Type u₁} [Category.{v₁} A] {B : Type u₂}
    [Category.{v₂} B] [Abelian A] [Abelian B] (T : A ⥤ B) [T.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T] {ι : Type*} (c : ComplexShape ι)
    (i : ι) :
    T.mapHomologicalComplex c ⋙ HomologicalComplex.homologyFunctor B c i ≅
      HomologicalComplex.homologyFunctor A c i ⋙ T :=
  NatIso.ofComponents (fun K ↦ (K.sc i).mapHomologyIso T)
    (fun φ ↦ ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor A c i).map φ) T)

/-- A morphism property respecting isomorphisms is invariant under naturally isomorphic
functors. -/
private theorem map_property_iff_of_iso {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] (P : MorphismProperty D) [P.RespectsIso] {F G : C ⥤ D} (e : F ≅ G)
    {A B : C} (f : A ⟶ B) : P (F.map f) ↔ P (G.map f) :=
  P.arrow_mk_iso_iff (Arrow.isoOfNatIso e (Arrow.mk f))

variable [HasDerivedCategory.{d} (OXMod.{u, u} X)]

/-- A morphism in the derived category out of a strictly perfect complex is, over a neighbourhood
of any point, realised by a morphism of complexes with the same behaviour on cohomology above and
at a given degree. -/
theorem exists_local_chain_map (hE : IsStrictlyPerfect E) (m : ℤ)
    (γ : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F)
    (hγiso : ∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map γ))
    (hγepi : Epi ((DerivedCategory.homologyFunctor _ m).map γ)) :
    ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ β : (Stacks.Cohomology.LocalNullHomotopy.restr X U).obj E ⟶
        (Stacks.Cohomology.LocalNullHomotopy.restr X U).obj F,
        (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap β j)) ∧
        Epi (HomologicalComplex.homologyMap β m) := by
  obtain ⟨G', g, s, hs, hγeq⟩ := DerivedCategory.left_fac γ
  have hsq : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).mp hs
  have hg : DerivedCategory.Q.map g = γ ≫ DerivedCategory.Q.map s := by
    rw [hγeq, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hQg : ∀ j : ℤ, (DerivedCategory.homologyFunctor (OXMod.{u, u} X) j).map
      (DerivedCategory.Q.map g) =
      (DerivedCategory.homologyFunctor (OXMod.{u, u} X) j).map γ ≫
        (DerivedCategory.homologyFunctor (OXMod.{u, u} X) j).map (DerivedCategory.Q.map s) :=
    fun j ↦ by rw [hg, Functor.map_comp]
  have hgiso : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap g j) := by
    intro j hj
    have := hγiso j hj
    refine (map_property_iff_of_iso (MorphismProperty.isomorphisms _)
      (DerivedCategory.homologyFunctorFactors (OXMod.{u, u} X) j) g).1 ?_
    change IsIso ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) j).map
      (DerivedCategory.Q.map g))
    rw [hQg j]
    infer_instance
  have hgepi : Epi (HomologicalComplex.homologyMap g m) := by
    have := hγepi
    refine (map_property_iff_of_iso (MorphismProperty.epimorphisms _)
      (DerivedCategory.homologyFunctorFactors (OXMod.{u, u} X) m) g).1 ?_
    change Epi ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) m).map
      (DerivedCategory.Q.map g))
    rw [hQg m]
    have : Epi ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) m).map
      (DerivedCategory.Q.map s)) := inferInstance
    infer_instance
  obtain ⟨a, ha⟩ := Stacks.Cohomology.LocalNullHomotopy.exists_lower_bound hE
  intro x
  obtain ⟨U, hxU, β, ⟨H⟩⟩ := exists_local_lift_homotopy g s a hE ha
    (fun j _ ↦ inferInstance) inferInstance x
  have hPH : (overFunctor.{u} (structureSheafOfRings X) U).PreservesHomology :=
    SheafOfModules.overFunctor_preservesHomology (structureSheafOfRings X) U
  have hPL : PreservesFiniteLimits (overFunctor.{u} (structureSheafOfRings X) U) :=
    SheafOfModules.overFunctor_preservesFiniteLimits (structureSheafOfRings X) U
  have hPE : (overFunctor.{u} (structureSheafOfRings X) U).PreservesEpimorphisms :=
    inferInstance
  have hsres : ∀ j : ℤ,
      IsIso (HomologicalComplex.homologyMap ((Stacks.Cohomology.LocalNullHomotopy.restr X U).map s)
        j) := fun j ↦
    (quasiIsoAt_iff_isIso_homologyMap _ j).mp inferInstance
  have hfac : ∀ j : ℤ, HomologicalComplex.homologyMap β j =
      HomologicalComplex.homologyMap ((Stacks.Cohomology.LocalNullHomotopy.restr X U).map g) j ≫
        inv (HomologicalComplex.homologyMap ((Stacks.Cohomology.LocalNullHomotopy.restr X U).map s)
          j) := by
    intro j
    have := hsres j
    have hcomp : HomologicalComplex.homologyMap β j ≫
        HomologicalComplex.homologyMap ((Stacks.Cohomology.LocalNullHomotopy.restr X U).map s) j =
        HomologicalComplex.homologyMap ((Stacks.Cohomology.LocalNullHomotopy.restr X U).map g) j :=
          by
      rw [← HomologicalComplex.homologyMap_comp]
      exact H.homologyMap_eq j
    rw [← hcomp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  refine ⟨U, hxU, β, fun j hj ↦ ?_, ?_⟩
  · have := hsres j
    have : QuasiIsoAt g j := (quasiIsoAt_iff_isIso_homologyMap g j).mpr (hgiso j hj)
    have : IsIso (HomologicalComplex.homologyMap ((Stacks.Cohomology.LocalNullHomotopy.restr X
      U).map g) j) :=
      (quasiIsoAt_iff_isIso_homologyMap _ j).mp inferInstance
    rw [hfac j]
    infer_instance
  · have := hsres m
    have h₂ : Epi (HomologicalComplex.homologyMap ((Stacks.Cohomology.LocalNullHomotopy.restr X
      U).map g) m) := by
      have := hgepi
      refine (map_property_iff_of_iso (MorphismProperty.epimorphisms _)
        (mapHomologicalComplexHomologyIso
          (overFunctor.{u} (structureSheafOfRings X) U) (ComplexShape.up ℤ) m) g).2 ?_
      rw [MorphismProperty.epimorphisms.iff]
      change Epi ((overFunctor.{u} (structureSheafOfRings X) U).map
        (HomologicalComplex.homologyMap g m))
      infer_instance
    rw [hfac m]
    infer_instance

end Stacks.PseudoCoherence.DerivedCharacterization

end
