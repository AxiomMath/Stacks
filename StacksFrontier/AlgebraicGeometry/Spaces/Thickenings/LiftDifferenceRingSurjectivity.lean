module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SharpCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureSharpInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSheafRingUnit
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CommRingPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomInverseImage

/-!
# The quotient map the difference of two lifts descends along

The descent of
`StacksFrontier/AlgebraicGeometry/Spaces/LiftDifferenceDescent.lean` is taken along a **locally
surjective** morphism of sheaves of rings `q : A ⟶ 𝒪_Y`.  In the situation of
[Stacks Project, Tag 0CKE] that morphism is the inverse-image form
`j^♯ : j^{-1}𝒪_W ⟶ 𝒪_{W₀}` of the structure map of the inclusion of a closed subspace, at the
coefficient category `RingCat` in which the sheaves of modules of this development are indexed.

Local surjectivity of that map is [Stacks Project, Tag 03MB] in inverse-image form, which
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionStructureSharpInverseImage.lean` proves at
`CommRingCat` and on underlying sheaves of sets.  This file carries it across the coefficient
split: `AlgebraicGeometry.Space.structureSharpRingInverseImage` is the `RingCat`-valued reading
of `AlgebraicGeometry.Space.structureSharpInverseImage`, by the identification of the
inverse-image form carried by the four-field morphism of small étale ringed topoi, so the two
have the same components and therefore the same image sieves.

It also records the general fact used to produce covering sieves on the smaller site: the
inverse image of sheaves of sets along a morphism of topoi is a left adjoint, hence preserves
epimorphisms, and on a site with sheafification an epimorphism of sheaves of sets is exactly a
locally surjective morphism.  So the inverse image of a locally surjective morphism is locally
surjective.

## Main results

* `AlgebraicGeometry.Space.structureSharpRingInverseImage_eq_forget₂`: the `RingCat`-valued
  inverse-image form of the structure map is the `CommRingCat`-valued one with commutativity
  forgotten.
* `AlgebraicGeometry.Space.structureSharpRingInverseImage_app`: consequently the two have the
  same value on every section.
* `AlgebraicGeometry.Space.isLocallySurjective_structureSharpRingInverseImage`: **the
  surjectivity clause of [Stacks Project, Tag 03MB] in inverse-image form at `RingCat`**, which
  is the hypothesis `[Sheaf.IsLocallySurjective q]` of
  `AlgebraicGeometry.Space.liftDifferenceDifferentialsHom`.
* `Stacks.Sheaves.ToposPullback.isLocallySurjective_inverseImage_map`: the inverse image of a
  locally surjective morphism of sheaves of sets is locally surjective.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.ToposPullback

universe ww vv uu vv' uu'

/-- **The inverse image of a locally surjective morphism of sheaves of sets is locally
surjective.**  On a site with sheafification local surjectivity is the same as being an
epimorphism, and the inverse image is a left adjoint, hence preserves epimorphisms. -/
theorem isLocallySurjective_inverseImage_map {Cc : Type uu} [Category.{vv} Cc]
    {Dd : Type uu'} [Category.{vv'} Dd]
    {Jc : GrothendieckTopology Cc} {Kc : GrothendieckTopology Dd}
    [HasSheafify Jc (Type ww)] [HasSheafify Kc (Type ww)]
    (f : MorphismOfTopoi (Sheaf Jc (Type ww)) (Sheaf Kc (Type ww)))
    {F G : Sheaf Kc (Type ww)} (φ : F ⟶ G) [Sheaf.IsLocallySurjective φ] :
    Sheaf.IsLocallySurjective (f.inverseImage.map φ) := by
  have : f.inverseImage.IsLeftAdjoint := ⟨_, ⟨f.adj⟩⟩
  exact (Sheaf.isLocallySurjective_iff_epi _).2 inferInstance

end Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.Space

universe u uu vv

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **The `RingCat`-valued inverse-image form of the structure map is the `CommRingCat`-valued
one with commutativity forgotten.**  Both are the inverse-image form of the structure map of
[Stacks Project, Tag 03G8] carried by the four-field morphism of small étale ringed topoi, read
at the two coefficient categories; the identification is
`AlgebraicGeometry.Space.fSharpInverseImage_eq_structureSharpRingInverseImage`.

This is the only statement bridging the two coefficient categories for the inverse-image form,
and it is what lets a statement proved on one side be read on the other. -/
theorem structureSharpRingInverseImage_eq_forget₂ (f : X ⟶ Y) :
    structureSharpRingInverseImage B S hS f =
      (sheafCompose (SmallEtale.topology B S hS X.1)
          (CategoryTheory.forget₂ CommRingCat.{u} RingCat.{u})).map
        (structureSharpInverseImage B S hS f) :=
  (fSharpInverseImage_eq_structureSharpRingInverseImage B S hS f).symm

/-- **The two coefficient readings of the inverse-image form of the structure map have the same
value on every section**, being the same morphism with commutativity forgotten. -/
theorem structureSharpRingInverseImage_app (f : X ⟶ Y)
    (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : ToType ((structureRingSheafInverseImage B S hS f).obj.obj V)) :
    (structureSharpRingInverseImage B S hS f).hom.app V x =
      (structureSharpInverseImageSet B S hS f).hom.app V x := by
  rw [structureSharpRingInverseImage_eq_forget₂]
  rfl

/-- **The surjectivity clause of [Stacks Project, Tag 03MB] in inverse-image form, at the
coefficient category `RingCat`.**  For the inclusion of a closed subspace — more generally for
a closed immersion `f : X ⟶ Y` — the structure map `f^♯ : f^{-1}𝒪_Y ⟶ 𝒪_X` is locally
surjective on the small étale site of `X`.

Local surjectivity only sees the underlying function, and the `RingCat`-valued form has the same
components as the one on sheaves of sets by
`AlgebraicGeometry.Space.structureSharpRingInverseImage_app`, so the image sieve of a section is
the same sieve on either side.

This is the hypothesis `[Sheaf.IsLocallySurjective q]` under which
`AlgebraicGeometry.Space.liftDifferenceDifferentialsHom` descends the difference of two lifts. -/
theorem isLocallySurjective_structureSharpRingInverseImage (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) :
    Sheaf.IsLocallySurjective (structureSharpRingInverseImage B S hS f) where
  imageSieve_mem {V} y := by
    have := isLocallySurjective_structureSharpInverseImageSet B S hS f hf
    have hsieve : Presheaf.imageSieve (structureSharpRingInverseImage B S hS f).hom y =
        Presheaf.imageSieve (structureSharpInverseImageSet B S hS f).hom y :=
      Sieve.ext fun _ _ => exists_congr fun t =>
        Eq.congr_left (structureSharpRingInverseImage_app B S hS f _ t)
    rw [hsieve]
    exact Presheaf.imageSieve_mem (SmallEtale.topology B S hS X.1)
      (structureSharpInverseImageSet B S hS f).hom y

/-- **The quotient map `j^♯ : j^{-1}𝒪_X ⟶ 𝒪_Z` of the inclusion of a closed subspace is locally
surjective**, as an instance: a closed subspace carries the closed immersion property of its
inclusion, so there is nothing left to supply. -/
instance isLocallySurjective_structureSharpRingInverseImage_subspaceInclusion
    (Z : ClosedSubspaces B S hS X.1) :
    Sheaf.IsLocallySurjective
      (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z)) :=
  isLocallySurjective_structureSharpRingInverseImage B S hS
    (subspaceInclusion B S hS X Z) Z.2.2

/-! ### The inverse image of the structure map along a further morphism -/

variable {Z' : AlgebraicSpaces B S hS}

/-- **The inverse image of the structure map of `f`, read on sections, is the inverse image of
its underlying map of sheaves of sets.**  This is
`Stacks.Sheaves.ToposPullback.underlyingRingSheaf_map_pullbackCommRingSheafMap` at the structure
map. -/
theorem app_inverseImage_structureSharpInverseImage (g : Z' ⟶ X) (f : X ⟶ Y)
    (V : (SmallEtale B S hS Z'.1)ᵒᵖ)
    (x : ToType (((smallEtaleInverseImageRing B S hS g).obj
      (inverseImageStructureSheaf B S hS f)).obj.obj V)) :
    ((smallEtaleInverseImageRing B S hS g).map
          (structureSharpInverseImage B S hS f)).hom.app V x =
      ((smallToposMorphismTypeU B S hS g).inverseImage.map
          (structureSharpInverseImageSet B S hS f)).hom.app V x :=
  setSheafHom_congr_app_apply
    (underlyingRingSheaf_map_pullbackCommRingSheafMap (SmallEtale.topology B S hS Z'.1)
      (Φ := (smallToposMorphismTypeU B S hS g).inverseImage)
      (structureSharpInverseImage B S hS f)) V x

/-- **The inverse image along any morphism of the structure map of a closed immersion is locally
surjective.**  The structure map of a closed immersion is locally surjective in inverse-image
form by [Stacks Project, Tag 03MB], and the inverse image preserves local surjectivity by
`Stacks.Sheaves.ToposPullback.isLocallySurjective_inverseImage_map`; local surjectivity only
sees the underlying function, which is the same on either side by
`AlgebraicGeometry.Space.app_inverseImage_structureSharpInverseImage`. -/
theorem isLocallySurjective_inverseImage_structureSharpInverseImage (g : Z' ⟶ X) (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) :
    Sheaf.IsLocallySurjective ((smallEtaleInverseImageRing B S hS g).map
      (structureSharpInverseImage B S hS f)) where
  imageSieve_mem {V} y := by
    have := isLocallySurjective_structureSharpInverseImageSet B S hS f hf
    have := isLocallySurjective_inverseImage_map (smallToposMorphismTypeU B S hS g)
      (structureSharpInverseImageSet B S hS f)
    have hsieve : Presheaf.imageSieve ((smallEtaleInverseImageRing B S hS g).map
          (structureSharpInverseImage B S hS f)).hom y =
        Presheaf.imageSieve ((smallToposMorphismTypeU B S hS g).inverseImage.map
          (structureSharpInverseImageSet B S hS f)).hom y :=
      Sieve.ext fun _ _ => exists_congr fun t =>
        Eq.congr_left (app_inverseImage_structureSharpInverseImage B S hS g f _ t)
    rw [hsieve]
    exact Presheaf.imageSieve_mem (SmallEtale.topology B S hS Z'.1)
      ((smallToposMorphismTypeU B S hS g).inverseImage.map
        (structureSharpInverseImageSet B S hS f)).hom y

/-- **The two coefficient readings of the inverse image of the structure map have the same value
on every section.**  Both are the inverse image of one and the same morphism of sheaves of sets,
by `AlgebraicGeometry.Space.structureSharpRingInverseImage_eq_forget₂`. -/
theorem app_inverseImage_structureSharpRingInverseImage (g : Z' ⟶ X) (f : X ⟶ Y)
    (V : (SmallEtale B S hS Z'.1)ᵒᵖ)
    (x : ToType (((smallEtaleInverseImageRing B S hS g).obj
      (inverseImageStructureSheaf B S hS f)).obj.obj V)) :
    ((inverseImageRingFunctor (smallToposMorphismTypeU B S hS g)).map
          (structureSharpRingInverseImage B S hS f)).hom.app V x =
      ((smallEtaleInverseImageRing B S hS g).map
          (structureSharpInverseImage B S hS f)).hom.app V x :=
  ((setSheafHom_congr_app_apply
      (ringSheafMap_pullbackRingSheafMap (SmallEtale.topology B S hS Z'.1)
        (smallToposMorphismTypeU B S hS g).inverseImage
        (structureSharpRingInverseImage B S hS f)) V x).trans
    (setSheafHom_congr_app_apply
      (congrArg (fun m => (smallToposMorphismTypeU B S hS g).inverseImage.map
          ((sheafCompose (SmallEtale.topology B S hS X.1)
            (CategoryTheory.forget RingCat.{u})).map m))
        (structureSharpRingInverseImage_eq_forget₂ B S hS f)) V x)).trans
    (app_inverseImage_structureSharpInverseImage B S hS g f V x).symm

end AlgebraicGeometry.Space

end

