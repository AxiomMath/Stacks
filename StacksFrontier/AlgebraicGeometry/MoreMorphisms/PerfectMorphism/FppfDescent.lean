module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.AffineCriteria
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.Flat
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.SyntomicDescent
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.FppfDescent

/-!
# Perfectness is local on the source for the fppf topology

Perfectness of morphisms of schemes is local on the source for the fppf topology. The affine
case is descent of perfectness along a surjective flat morphism locally of finite presentation of
affine schemes.

## Main results

* `AlgebraicGeometry.Perfect.respectsLeft_flat_inf_locallyOfFinitePresentation`: precomposition
  with a flat morphism locally of finite presentation preserves perfectness.
* `AlgebraicGeometry.perfect_of_comp_surjective_flat_of_isAffine`: the affine case, that a
  perfect composite `g ≫ f` with `g` a surjective flat morphism locally of finite presentation
  of affine schemes forces `f` perfect.
* `AlgebraicGeometry.Perfect.isLocalAtSource_fppfPrecoverage`: perfectness is local on the source
  for the fppf topology.

## References

* [The Stacks Project, Lemma 37.61.14 (069D)](https://stacks.math.columbia.edu/tag/069D)
* [The Stacks Project, Lemma 35.26.4 (036H)](https://stacks.math.columbia.edu/tag/036H)
* [The Stacks Project, Lemma 37.60.14 (0699)](https://stacks.math.columbia.edu/tag/0699)
* [The Stacks Project, Lemma 37.61.4 (068A)](https://stacks.math.columbia.edu/tag/068A)
* [The Stacks Project, Lemma 37.61.3 (0689)](https://stacks.math.columbia.edu/tag/0689)
-/

@[expose] public section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-- Precomposition with a flat morphism locally of finite presentation preserves perfectness of
morphisms of schemes. -/
theorem Perfect.respectsLeft_flat_inf_locallyOfFinitePresentation :
    MorphismProperty.RespectsLeft (@Perfect.{u} : MorphismProperty Scheme.{u})
      (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) where
  precomp i hi f hf := by
    have : Flat i := hi.1
    have : LocallyOfFinitePresentation i := hi.2
    have : Perfect f := hf
    infer_instance

/-- If `g : X' ⟶ X` is a surjective flat morphism locally of finite presentation of affine
schemes and `g ≫ f : X' ⟶ Y` is perfect, then `f : X ⟶ Y` is perfect. -/
@[ega "IV 17.7.5" "special case"]
theorem perfect_of_comp_surjective_flat_of_isAffine {X' X Y : Scheme.{u}}
    [IsAffine X'] [IsAffine X] [IsAffine Y] (g : X' ⟶ X) (f : X ⟶ Y)
    (hgsurj : Surjective g) (hgflat : Flat g) (hglfp : LocallyOfFinitePresentation g)
    (hcomp : Perfect (g ≫ f)) : Perfect f := by
  have hpc : PseudoCoherent f := by
    have : Surjective g := hgsurj
    have : Flat g := hgflat
    have : LocallyOfFinitePresentation g := hglfp
    refine MorphismProperty.IsLocalAtSource.of_forall_comp (P := @PseudoCoherent.{u})
      g.singleton_mem_fppfPrecoverage ?_
    rintro U h ⟨⟩
    have : Perfect (g ≫ f) := hcomp
    exact inferInstance
  have hff : (g.appTop).hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g).mp ⟨hgflat, hgsurj⟩
  have hcomp' : PerfectRingHom (g.appTop.hom.comp f.appTop.hom) := by
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
      HasRingHomProperty.appTop (P := @Perfect) (g ≫ f) hcomp
  rw [HasRingHomProperty.iff_of_isAffine (P := @Perfect) (Q := @PerfectRingHom)]
  exact ⟨HasRingHomProperty.appTop (P := @PseudoCoherent) f hpc,
    finiteTorDimensionRingHom_of_faithfullyFlat f.appTop.hom g.appTop.hom hff hcomp'.2⟩

/-- Perfectness of morphisms of schemes is local on the source for the fppf topology: a morphism
is perfect exactly when its composites with the members of an fppf covering of its source are. -/
@[stacks 069D]
instance Perfect.isLocalAtSource_fppfPrecoverage :
    MorphismProperty.IsLocalAtSource (@Perfect.{u} : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
  let := Perfect.respectsLeft_flat_inf_locallyOfFinitePresentation.{u}
  isLocalAtSource_fppf_of_affine_descent (@Perfect.{u}) perfect_of_comp_surjective_flat_of_isAffine

end AlgebraicGeometry

end
