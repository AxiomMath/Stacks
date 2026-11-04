module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
public import Mathlib.CategoryTheory.Subobject.Lattice
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic

/-!
# The largest quasi-coherent subsheaf

Every submodule of a quasi-coherent module on a scheme contains a unique largest quasi-coherent
submodule. It is characterized by the fact that every morphism from a quasi-coherent module
factors uniquely through it.

The candidate is the supremum of all quasi-coherent subobjects of the given one. The supremum of
a set of subobjects is the image of the canonical morphism out of their coproduct, so it is
quasi-coherent because quasi-coherence is closed under coproducts and under images; the universal
property then forces uniqueness.

## Main results

* `AlgebraicGeometry.existsUnique_quasicoherentSubobject`: existence and uniqueness of the
  largest quasi-coherent subobject contained in a given subobject.

## Implementation notes

Submodules are represented categorically as subobjects. The universal property is stated as
bijectivity of composition with the subobject arrow; this records both existence and uniqueness
of the factorization.

The set of quasi-coherent subobjects need not be small, so the coproduct is taken over its image
under `equivShrink`, as `CategoryTheory.Subobject.smallCoproductDesc` requires.

## References

* [Stacks Project, Tag 01QZ](https://stacks.math.columbia.edu/tag/01QZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The image subobject of a morphism from a quasi-coherent module into a subobject of a
quasi-coherent module is quasi-coherent. -/
private lemma isQuasicoherent_imageSubobject (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent] (G : Subobject F) (H : X.Modules) [H.IsQuasicoherent]
    (f : H ⟶ (G : X.Modules)) :
    (imageSubobject f : X.Modules).IsQuasicoherent := by
  let e : image f ≅ image (f ≫ G.arrow) :=
    image.isoStrongEpiMono (factorThruImage f) (image.ι f ≫ G.arrow) (by simp)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (e.symm ≪≫ (imageSubobjectIso f).symm) (isQuasicoherent_image (f ≫ G.arrow))

/-- A supremum of quasi-coherent subobjects is quasi-coherent. -/
private lemma isQuasicoherent_sSup_subobject (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent] (G : Subobject F) (S : Set (Subobject (G : X.Modules)))
    (hS : ∀ P ∈ S, (P : X.Modules).IsQuasicoherent) :
    ((sSup S : Subobject (G : X.Modules)) : X.Modules).IsQuasicoherent := by
  let E := equivShrink.{u} (Subobject (G : X.Modules))
  let A : (E '' S) → X.Modules := fun j ↦ (E.symm j : X.Modules)
  have hA (j : E '' S) : (A j).IsQuasicoherent :=
    hS _ ((Subobject.symm_apply_mem_iff_mem_image E S j).mpr j.2)
  have : (∐ A).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_colimit
      (Discrete.functor A) (fun j ↦ hA j.as)
  exact isQuasicoherent_imageSubobject X F G (∐ A) (Subobject.smallCoproductDesc S)

/-- A subobject of a quasi-coherent module on a scheme contains a unique
quasi-coherent subobject through which every morphism from a quasi-coherent
module factors uniquely. -/
@[stacks 01QZ]
public lemma existsUnique_quasicoherentSubobject (X : AlgebraicGeometry.Scheme.{u})
    (F : X.Modules) [F.IsQuasicoherent] (G : Subobject F) :
    ∃! G' : { G' : Subobject (G : X.Modules) // (G' : X.Modules).IsQuasicoherent },
      ∀ (H : X.Modules) [H.IsQuasicoherent],
        Function.Bijective (fun f : H ⟶ (G'.1 : X.Modules) ↦ f ≫ G'.1.arrow) := by
  let S : Set (Subobject (G : X.Modules)) := {P | (P : X.Modules).IsQuasicoherent}
  let G' : { G' : Subobject (G : X.Modules) // (G' : X.Modules).IsQuasicoherent } :=
    ⟨sSup S, isQuasicoherent_sSup_subobject X F G S fun _ hP ↦ hP⟩
  have hG' : ∀ (H : X.Modules) [H.IsQuasicoherent],
      Function.Bijective (fun f : H ⟶ (G'.1 : X.Modules) ↦ f ≫ G'.1.arrow) := by
    intro H hH
    let inv (f : H ⟶ (G : X.Modules)) : H ⟶ (G'.1 : X.Modules) :=
      G'.1.factorThru f (Subobject.factors_of_le f
        (Subobject.le_sSup S (Limits.imageSubobject f)
          (isQuasicoherent_imageSubobject X F G H f))
          (by simpa using Limits.imageSubobject_factors_comp_self f (𝟙 H)))
    exact ⟨fun _ _ h ↦ Subobject.eq_of_comp_arrow_eq h,
      fun f ↦ ⟨inv f, G'.1.factorThru_arrow _ _⟩⟩
  refine ⟨G', hG', fun K hK ↦ ?_⟩
  have : (K.1 : X.Modules).IsQuasicoherent := K.2
  have : (G'.1 : X.Modules).IsQuasicoherent := G'.2
  obtain ⟨f, hf⟩ := (hG' (K.1 : X.Modules)).2 K.1.arrow
  obtain ⟨g, hg⟩ := (hK (G'.1 : X.Modules)).2 G'.1.arrow
  exact Subtype.ext (le_antisymm (Subobject.le_of_comm f hf) (Subobject.le_of_comm g hg))

end AlgebraicGeometry
