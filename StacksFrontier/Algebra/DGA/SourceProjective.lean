module

public import StacksFrontier.Algebra.DGA.DerivedCategory
public import StacksFrontier.CategoryTheory.Triangulated.AdmissibleSubcategories
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Fractions
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import StacksCore.Tactic.StacksAttribute

/-!
# Source-projective differential graded modules

Let `A` be a differential graded algebra.  An object of the homotopy category of right
differential graded `A`-modules is *source-projective* when localization at the
quasi-isomorphisms is bijective on morphisms out of it into every differential graded module.
This file introduces that class, characterises it by the vanishing of all maps to acyclic
objects, and records that it is a strictly full saturated triangulated subcategory.

## Main definitions

* `Stacks.DifferentialGradedModule.SourceProjective.sourceProjective`: the source-projective
  objects, as an object property.

## Main results

* `Stacks.DifferentialGradedModule.SourceProjective.sourceProjective_iff_hom_acyclic_subsingleton`:
  a differential graded module is
  source-projective exactly when every morphism from it to an acyclic differential graded module
  vanishes in the homotopy category.
* `Stacks.DifferentialGradedModule.SourceProjective.sourceProjective_isClosedUnderIsomorphisms`,
  `Stacks.DifferentialGradedModule.SourceProjective.sourceProjective_isTriangulated`,
  `Stacks.DifferentialGradedModule.SourceProjective.sourceProjective_isSaturated`: the
  class is strictly full, triangulated and saturated.

## Implementation notes

The criterion is proved in two halves.  Vanishing of the maps to acyclic objects gives
bijectivity of postcomposition with a quasi-isomorphism, by the coyoneda exactness of the
distinguished triangle that the quasi-isomorphism completes to — its third vertex is acyclic
because the quasi-isomorphisms are the class `(acyclic A).trW`
(`DifferentialGradedModule.acyclic_trW_eq_quasiIsomorphisms`).  Bijectivity of postcomposition
with every quasi-isomorphism in turn gives bijectivity of the localization map, by the left
calculus of fractions on the quasi-isomorphisms: a morphism of the localization is a left
fraction, and an equality of localized morphisms becomes an equality after postcomposition with
some quasi-isomorphism.

The converse half is the identification of the localization's kernel with the acyclic objects,
`DifferentialGradedModule.localization_kernel_eq_acyclic`.

Strict fullness, the triangulated-subcategory property and saturation are all read off the
equality of the source-projective objects with the left orthogonal of the acyclic objects, for
which `StacksFrontier/CategoryTheory/Triangulated/AdmissibleSubcategories.lean` supplies the
instances.  Saturation is stability under retracts together with closure under isomorphisms, and
the left orthogonal of any object property is stable under retracts.

## References

* [Stacks Project, Tag 09R0](https://stacks.math.columbia.edu/tag/09R0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated

universe u v w

namespace Stacks.DifferentialGradedModule.SourceProjective

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra.{u, v} R)

/-- The source-projective objects of the homotopy category of right differential graded
`A`-modules: those from which morphisms are unchanged by passage to the derived category. -/
@[stacks 09R0 "source_projective_dg_modules"]
abbrev sourceProjective :
    ObjectProperty (DifferentialGradedModule.HomotopyCategory.{u, v, w} A) :=
  fun P => ∀ M : DifferentialGradedModule.{u, v, w} A,
    Function.Bijective
      ((DifferentialGradedModule.quasiIsomorphisms A).Q.map :
        (P ⟶ (DifferentialGradedModule.toHomotopyCategory A).obj M) →
          ((DifferentialGradedModule.quasiIsomorphisms A).Q.obj P ⟶
            (DifferentialGradedModule.quasiIsomorphisms A).Q.obj
              ((DifferentialGradedModule.toHomotopyCategory A).obj M)))

/-- If every morphism from `P` to an acyclic object vanishes, then postcomposition with a
quasi-isomorphism is bijective on morphisms out of `P`. -/
private theorem hom_postcomp_bijective_of_acyclic
    (P X Y : DifferentialGradedModule.HomotopyCategory.{u, v, w} A) (s : X ⟶ Y)
    (hs : DifferentialGradedModule.quasiIsomorphisms A s)
    (hvan : ∀ N : DifferentialGradedModule.HomotopyCategory.{u, v, w} A,
      DifferentialGradedModule.acyclic A N → Subsingleton (P ⟶ N)) :
    Function.Bijective (fun f : P ⟶ X => f ≫ s) := by
  obtain ⟨Z, g, h, hT, hZ⟩ : (DifferentialGradedModule.acyclic A).trW s := by
    rwa [DifferentialGradedModule.acyclic_trW_eq_quasiIsomorphisms]
  change Triangle.mk s g h ∈ distTriang _ at hT
  constructor
  · intro f₁ f₂ heq
    change f₁ ≫ s = f₂ ≫ s at heq
    have hd : (f₁ - f₂) ≫ (Triangle.mk s g h).mor₁ = 0 := by
      change (f₁ - f₂) ≫ s = 0
      rw [Preadditive.sub_comp, heq, sub_self]
    obtain ⟨k, hk⟩ := Triangle.coyoneda_exact₂ (Triangle.mk s g h).invRotate
      (inv_rot_of_distTriang _ hT) (f₁ - f₂) hd
    rw [← sub_eq_zero, hk, (hvan (Triangle.mk s g h).invRotate.obj₁
      ((DifferentialGradedModule.acyclic A).le_shift (-1) Z hZ)).elim k 0]
    exact Limits.zero_comp
  · intro f
    obtain ⟨g', hg'⟩ := Triangle.coyoneda_exact₂ (Triangle.mk s g h) hT f
      ((hvan Z hZ).elim (f ≫ (Triangle.mk s g h).mor₂) 0)
    exact ⟨g', hg'.symm⟩

/-- If postcomposition with every quasi-isomorphism is bijective on morphisms out of `P`, then
the localization functor is bijective on morphisms out of `P`. -/
private theorem localization_map_bijective_of_postcomp
    (P M : DifferentialGradedModule.HomotopyCategory.{u, v, w} A)
    (hpost : ∀ (N N' : DifferentialGradedModule.HomotopyCategory.{u, v, w} A) (s : N ⟶ N'),
      DifferentialGradedModule.quasiIsomorphisms A s →
        Function.Bijective (fun f : P ⟶ N => f ≫ s)) :
    Function.Bijective
      (fun f : P ⟶ M => (DifferentialGradedModule.quasiIsomorphisms A).Q.map f) := by
  constructor
  · intro f g hfg
    obtain ⟨Z, s, hs, h⟩ :=
      (MorphismProperty.map_eq_iff_postcomp
        (L := (DifferentialGradedModule.quasiIsomorphisms A).Q)
        (W := DifferentialGradedModule.quasiIsomorphisms A) f g).mp hfg
    exact (hpost M Z s hs).injective h
  · intro f
    obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction
      (DifferentialGradedModule.quasiIsomorphisms A).Q
      (DifferentialGradedModule.quasiIsomorphisms A) f
    obtain ⟨g, hg⟩ := (hpost M φ.Y' φ.s φ.hs).surjective φ.f
    refine ⟨g, ?_⟩
    rw [hφ]
    have hiso : IsIso ((DifferentialGradedModule.quasiIsomorphisms A).Q.map φ.s) :=
      Localization.inverts (DifferentialGradedModule.quasiIsomorphisms A).Q
        (DifferentialGradedModule.quasiIsomorphisms A) φ.s φ.hs
    apply (cancel_mono ((DifferentialGradedModule.quasiIsomorphisms A).Q.map φ.s)).1
    rw [← Functor.map_comp, show g ≫ φ.s = φ.f from hg,
      MorphismProperty.LeftFraction.map_comp_map_s]

/-- **Stacks Project, Tag 09R0.** A differential graded module has the same morphisms out of it
in the homotopy and the derived category exactly when every morphism from it to an acyclic
differential graded module vanishes in the homotopy category. -/
theorem sourceProjective_iff_hom_acyclic_subsingleton
    (P : DifferentialGradedModule.{u, v, w} A) :
    (∀ M : DifferentialGradedModule.{u, v, w} A,
      Function.Bijective
        (fun f : (DifferentialGradedModule.toHomotopyCategory A).obj P ⟶
            (DifferentialGradedModule.toHomotopyCategory A).obj M =>
          (DifferentialGradedModule.quasiIsomorphisms A).Q.map f)) ↔
      (∀ N : DifferentialGradedModule.{u, v, w} A,
        DifferentialGradedModule.acyclic A
            ((DifferentialGradedModule.toHomotopyCategory A).obj N) →
          Subsingleton ((DifferentialGradedModule.toHomotopyCategory A).obj P ⟶
            (DifferentialGradedModule.toHomotopyCategory A).obj N)) := by
  constructor
  · intro h N hN
    have hzero : Limits.IsZero ((DifferentialGradedModule.quasiIsomorphisms A).Q.obj
        ((DifferentialGradedModule.toHomotopyCategory A).obj N)) := by
      rw [← DifferentialGradedModule.localization_kernel_eq_acyclic A] at hN
      simpa only [Functor.kernel, ObjectProperty.inverseImage] using hN
    exact ⟨fun f g => (h N).injective (hzero.eq_of_tgt _ _)⟩
  · intro h M
    exact localization_map_bijective_of_postcomp A _
      ((DifferentialGradedModule.toHomotopyCategory A).obj M)
      (fun N N' s hs => hom_postcomp_bijective_of_acyclic A _ N N' s hs fun N hN => h N.as hN)

add_to_stacks 09R0 "acyclic_target_criterion"
  Stacks.DifferentialGradedModule.SourceProjective.sourceProjective_iff_hom_acyclic_subsingleton

/-- The source-projective objects are exactly the left orthogonal of the acyclic objects. -/
private theorem sourceProjective_eq_acyclic_leftOrthogonal :
    sourceProjective.{u, v, w} A =
      (DifferentialGradedModule.acyclic.{u, v, w} A).leftOrthogonal := by
  funext X
  apply propext
  have haux := sourceProjective_iff_hom_acyclic_subsingleton A X.as
  change (∀ M : DifferentialGradedModule.{u, v, w} A,
      Function.Bijective (fun f : X ⟶ (DifferentialGradedModule.toHomotopyCategory A).obj M =>
        (DifferentialGradedModule.quasiIsomorphisms A).Q.map f)) ↔ _ at haux
  rw [ObjectProperty.leftOrthogonal_iff]
  exact haux.trans
    ⟨fun h N f hN => (h N.as hN).elim f 0,
      fun h N hN => ⟨fun f g => by rw [h f hN, h g hN]⟩⟩

/-- **Stacks Project, Tag 09R0.** Source-projectivity is invariant under isomorphism in the
homotopy category. -/
@[stacks 09R0 "triangulated_saturated"]
instance sourceProjective_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (sourceProjective.{u, v, w} A) :=
  sourceProjective_eq_acyclic_leftOrthogonal A ▸ inferInstance

/-- **Stacks Project, Tag 09R0.** The source-projective objects form a triangulated
subcategory of the homotopy category. -/
@[stacks 09R0 "triangulated_saturated"]
instance sourceProjective_isTriangulated :
    (sourceProjective.{u, v, w} A).IsTriangulated := by
  rw [sourceProjective_eq_acyclic_leftOrthogonal A]
  infer_instance

/-- **Stacks Project, Tag 09R0.** The triangulated subcategory of source-projective objects is
saturated. -/
@[stacks 09R0 "triangulated_saturated"]
instance sourceProjective_isSaturated :
    (sourceProjective.{u, v, w} A).IsSaturated := by
  rw [sourceProjective_eq_acyclic_leftOrthogonal A]
  have h₂ : ObjectProperty.IsStableUnderRetracts
      (DifferentialGradedModule.acyclic.{u, v, w} A).leftOrthogonal.isoClosure := by
    rw [ObjectProperty.isoClosure_eq_self]
    exact (ObjectProperty.isStableUnderRetracts_rightOrthogonal_and_leftOrthogonal
      (DifferentialGradedModule.acyclic.{u, v, w} A)).2
  exact
    { isoClosure_of_biprod_left := fun h =>
        ObjectProperty.IsStableUnderRetracts.of_biprod_left _ h
      isoClosure_of_biprod_right := fun h =>
        ObjectProperty.IsStableUnderRetracts.of_biprod_right _ h }

end Stacks.DifferentialGradedModule.SourceProjective

end
