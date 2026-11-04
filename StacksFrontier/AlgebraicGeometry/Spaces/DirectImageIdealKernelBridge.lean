module

public import StacksFrontier.AlgebraicGeometry.Spaces.InverseImageDefiningIdealKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.InverseImageStructureSharpSection
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionCommRingCounit
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformSupportedLift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModuleUnit

/-!
# The kernel of `i_*i⁻¹𝒪_X ⟶ i_*𝒪_Z`, presented by `i_*i⁻¹𝓘`

Let `Z ⊆ X` be a closed subspace of an algebraic space with inclusion `i` and defining ideal
sheaf `𝓘`.  `StacksFrontier/AlgebraicGeometry/Spaces/InverseImageDefiningIdealKernel.lean` carries
the short exact sequence `0 ⟶ 𝓘 ⟶ 𝒪_X ⟶ i_*𝒪_Z ⟶ 0` of Stacks 03MB through the inverse image
along `i` and then through the direct image, and reads the result on sections: over every object
of the small étale site of `X`, the inclusion `(i_*i⁻¹𝓘)(U) ⟶ (i_*i⁻¹𝒪_X)(U)` is injective with
range exactly the kernel of the third map.

That third map is `i_*i⁻¹` of the **direct-image** form `i♯ : 𝒪_X ⟶ i_*𝒪_Z` of the structure map.
What the derivation of Stacks 02HP runs on is the **inverse-image** form
`AlgebraicGeometry.Space.structureSharpInverseImage`, pushed forward:
`i_*(i♯) : i_*i⁻¹𝒪_X ⟶ i_*𝒪_Z`, which is the split surjection a left inverse of `i` splits.  This
file identifies the two on sections — they differ by the direct image of the counit `i⁻¹i_*𝒪_Z ≅
𝒪_Z`, which is invertible for a closed immersion — and so presents the kernel of the split
surjection by `i_*i⁻¹𝓘`, in exactly the sectionwise shape
`PresheafOfModules.splitIdealDerivation` consumes.

## Main results

* `AlgebraicGeometry.Space.directImageStructureSharpInverseImage_val_app`: **the pushed-forward
  inverse-image form of the structure map, on sections, is the third map of the complex of
  Stacks 03MB carried through `i_*i⁻¹`, followed by the direct image of the counit.**
* `AlgebraicGeometry.Space.injective_directImageInverseImageIdealIota`,
  `AlgebraicGeometry.Space.exists_directImageInverseImageIdealIota` and
  `AlgebraicGeometry.Space.directImageInverseImageIdealIota_eq_zero`: the sections of
  `i_*i⁻¹𝓘` are, through the inclusion, **exactly** the kernel of that split surjection.
* `AlgebraicGeometry.Space.directImageInverseImageIdealIota_add`,
  `…_smul` and `…_map`: the inclusion is additive, semilinear and compatible with restriction.
* `AlgebraicGeometry.Space.ringSheaf_directImageInverseImageStructureSheaf` and
  `AlgebraicGeometry.Space.directInverseUnitModule`: the two identifications of objects the
  above rest on.

## Implementation notes

**The counit is where the two forms of the structure map differ, and it is the only place a
closed immersion is used.**  `AlgebraicGeometry.RingedToposHom.fSharpInverseImage` is by
definition the adjunct of the direct-image form, so it is `i⁻¹(i♯)` followed by the counit
(`CategoryTheory.Adjunction.homEquiv_counit`); pushing that forward gives
`AlgebraicGeometry.Space.directImageStructureSharpInverseImage_eq`.  The counit of a closed
immersion is invertible by Stacks 04E5 part (1)
(`AlgebraicGeometry.Space.commRingCounitIso`), so its direct image is injective on sections, and
the two kernels coincide.

**Why everything downstream is stated on sections, with the module left at its own spelling.**
`i_*i⁻¹𝓘` is a module over `pushforwardRingSheaf i (inverseImageRingSheaf i 𝒪_X)`, while the
split surjection lives on the sheaf of *commutative* rings
`AlgebraicGeometry.Space.directImageInverseImageStructureSheaf`.  The two sheaves of rings are
equal — `ringSheaf_directImageInverseImageStructureSheaf`, `rfl`, in a declaration of its own —
and so are the inclusion's target and the unit module (`directInverseUnitModule`, two
applications of `Stacks.Sheaves.ToposPullback.pullbackModuleObj_unit`).  But **ascribing** the
module or the inclusion to the second spelling exhausts the heartbeat budget at `isDefEq`, even
with the object equality already proved and even with nothing else in the declaration.  So the
module keeps the spelling its construction gives it, and what is exported is the inclusion *on
sections* together with its algebraic properties — which is also exactly the interface
`PresheafOfModules.splitIdealDerivation` was given for this reason.

**The direct image of the counit is injective on sections by its inverse law taken at the
presheaf level** (`CategoryTheory.ObjectProperty.isoHom_inv_id_hom`), and only then read on
sections.  Taking it at the sheaf level instead makes the elaborator project `.hom.app U` out of a
composite of morphisms of sheaves by unfolding them, which exhausts the heartbeat budget.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), the defining ideal
  sheaf as the kernel of the structure map.
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5), part (1), which makes
  the counit invertible.
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map of a
  morphism of algebraic spaces in its two forms.
* [Stacks Project, Tag 02HP](https://stacks.math.columbia.edu/tag/02HP), the derivation built on
  this presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1)

/-- The morphism of small étale topoi of the inclusion of a closed subspace. -/
noncomputable abbrev subspaceToposHom :
    MorphismOfTopoi
      (Sheaf (SmallEtale.topology B S hS (subspaceSpace B S hS Z).1) (Type u))
      (Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :=
  (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X Z)).toToposHom

/-- The sections over `U` of the direct image along `i` of the inverse image along `i`. -/
noncomputable abbrev directInverseSections (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (G : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) : Type u :=
  (Sheaf.sectionsFunctor (SmallEtale.topology B S hS X.1) U).obj
    ((subspaceToposHom B S hS X Z).pushforward.obj
      ((subspaceToposHom B S hS X Z).inverseImage.obj G))

/-- The sections over `U` of `i_*i⁻¹` of a homomorphism of sheaves of rings on the small étale
site of `X` out of the structure sheaf. -/
noncomputable def ringDirectInverseSection
    {Rt : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u}}
    (t : structureRingSheaf B S hS X ⟶ Rt)
    (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (z : ToType ((directImageInverseImageStructureSheaf B S hS
      (subspaceInclusion B S hS X Z)).obj.obj U)) :
    directInverseSections B S hS X Z U (Sheaf.ringSheaf Rt) :=
  (Sheaf.sectionsFunctor (SmallEtale.topology B S hS X.1) U).map
    ((subspaceToposHom B S hS X Z).pushforward.map
      ((subspaceToposHom B S hS X Z).inverseImage.map
        ((sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).map t))) z

/-- The third map of the direct image of the inverse image of the sequence of Stacks 03MB, read
on sections, is `i_*i⁻¹` of the `RingCat`-valued structure map. -/
theorem directImageDefiningIdealComplex_g_val_app (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (z : ToType ((directImageInverseImageStructureSheaf B S hS
      (subspaceInclusion B S hS X Z)).obj.obj U)) :
    ((directImageDefiningIdealComplex B S hS X Z).g.val.app U).hom z =
      ringDirectInverseSection B S hS X Z
        (structureSharp B S hS (subspaceInclusion B S hS X Z)) U z := rfl

/-- `i_*i⁻¹` of a homomorphism of sheaves of *commutative* rings, read on sections, is
`i_*i⁻¹` of the underlying homomorphism of sheaves of rings. -/
theorem pushforwardInverseImageCommRing_val_app
    (h : (smallEtaleRingedTopos B S hS X).O ⟶
      (pushforwardCommRingFunctor (subspaceToposHom B S hS X Z)).obj
        (smallEtaleRingedTopos B S hS (subspaceSpace B S hS Z)).O)
    (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (z : ToType ((directImageInverseImageStructureSheaf B S hS
      (subspaceInclusion B S hS X Z)).obj.obj U)) :
    ((((pushforwardCommRingFunctor (subspaceToposHom B S hS X Z)).map
        ((inverseImageCommRingFunctor (subspaceToposHom B S hS X Z)).map h)).hom.app
      U).hom) z =
      ringDirectInverseSection B S hS X Z
        ((sheafCompose (SmallEtale.topology B S hS X.1)
          (forget₂ CommRingCat.{u} RingCat.{u})).map h) U z := by
  have key : (sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).map
        ((Stacks.forgetCommRingSheaf.{u, u + 1, u} (SmallEtale.topology B S hS X.1)).map
          ((pushforwardCommRingFunctor (subspaceToposHom B S hS X Z)).map
            ((inverseImageCommRingFunctor (subspaceToposHom B S hS X Z)).map h))) =
      (subspaceToposHom B S hS X Z).pushforward.map
        ((subspaceToposHom B S hS X Z).inverseImage.map
          ((sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).map
            ((Stacks.forgetCommRingSheaf.{u, u + 1, u}
              (SmallEtale.topology B S hS X.1)).map h))) := by
    have e0 : (pushforwardCommRingFunctor (subspaceToposHom B S hS X Z)).map
          ((inverseImageCommRingFunctor (subspaceToposHom B S hS X Z)).map h) =
        pullbackCommRingSheafMap (SmallEtale.topology B S hS X.1)
          (subspaceToposHom B S hS X Z).pushforward
          (pullbackCommRingSheafMap
            (SmallEtale.topology B S hS (subspaceSpace B S hS Z).1)
            (subspaceToposHom B S hS X Z).inverseImage h) := rfl
    rw [e0]
    refine Eq.trans (congrArg
      (sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).map
      (Eq.trans
        (forgetCommRingSheaf_map_pullbackCommRingSheafMap (SmallEtale.topology B S hS X.1)
          (subspaceToposHom B S hS X Z).pushforward
          (pullbackCommRingSheafMap
            (SmallEtale.topology B S hS (subspaceSpace B S hS Z).1)
            (subspaceToposHom B S hS X Z).inverseImage h))
        (congrArg (pullbackRingSheafMap (SmallEtale.topology B S hS X.1)
            (subspaceToposHom B S hS X Z).pushforward)
          (forgetCommRingSheaf_map_pullbackCommRingSheafMap
            (SmallEtale.topology B S hS (subspaceSpace B S hS Z).1)
            (subspaceToposHom B S hS X Z).inverseImage h)))) ?_
    refine Eq.trans (ringSheafMap_pullbackRingSheafMap (SmallEtale.topology B S hS X.1)
      (subspaceToposHom B S hS X Z).pushforward
      (pullbackRingSheafMap (SmallEtale.topology B S hS (subspaceSpace B S hS Z).1)
        (subspaceToposHom B S hS X Z).inverseImage
        ((Stacks.forgetCommRingSheaf.{u, u + 1, u}
          (SmallEtale.topology B S hS X.1)).map h))) ?_
    exact congrArg (subspaceToposHom B S hS X Z).pushforward.map
      (ringSheafMap_pullbackRingSheafMap
        (SmallEtale.topology B S hS (subspaceSpace B S hS Z).1)
        (subspaceToposHom B S hS X Z).inverseImage
        ((Stacks.forgetCommRingSheaf.{u, u + 1, u} (SmallEtale.topology B S hS X.1)).map h))
  exact congrArg
    (fun m ↦ (Sheaf.sectionsFunctor (SmallEtale.topology B S hS X.1) U).map m z) key

/-! ### The counit, and the inverse-image form of the structure map on sections -/

/-- `i_*i⁻¹i_*𝒪_Z`, the third term of the direct image of the inverse image of the sequence of
Stacks 03MB, as a sheaf of commutative rings. -/
noncomputable abbrev directInverseDirectStructureSheaf :
    Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u} :=
  (pushforwardCommRingFunctor (subspaceToposHom B S hS X Z)).obj
    ((inverseImageCommRingFunctor (subspaceToposHom B S hS X Z)).obj
      ((pushforwardCommRingFunctor (subspaceToposHom B S hS X Z)).obj
        (smallEtaleRingedTopos B S hS (subspaceSpace B S hS Z)).O))

/-- The direct image along `i` of the counit `i⁻¹i_*𝒪_Z ≅ 𝒪_Z` of a closed immersion. -/
noncomputable def directImageCommRingCounitIso :
    directInverseDirectStructureSheaf B S hS X Z ≅
      (pushforwardCommRingFunctor (subspaceToposHom B S hS X Z)).obj
        (smallEtaleRingedTopos B S hS (subspaceSpace B S hS Z)).O :=
  (pushforwardCommRingFunctor (subspaceToposHom B S hS X Z)).mapIso
    (commRingCounitIso B S hS (subspaceInclusion B S hS X Z) Z.2.2
      (smallEtaleRingedTopos B S hS (subspaceSpace B S hS Z)).O)

/-- The isomorphism is the direct image of the counit. -/
theorem directImageCommRingCounitIso_hom :
    (directImageCommRingCounitIso B S hS X Z).hom =
      (pushforwardCommRingFunctor (subspaceToposHom B S hS X Z)).map
        ((commRingImageAdjunction (subspaceToposHom B S hS X Z)).counit.app
          (smallEtaleRingedTopos B S hS (subspaceSpace B S hS Z)).O) := rfl

/-- The direct image of the counit is injective on sections over every object. -/
theorem injective_directImageCommRingCounitIso_hom_app (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a b : ToType ((directInverseDirectStructureSheaf B S hS X Z).obj.obj U))
    (hab : ((directImageCommRingCounitIso B S hS X Z).hom.hom.app U).hom a =
      ((directImageCommRingCounitIso B S hS X Z).hom.hom.app U).hom b) : a = b := by
  have hcomp : (directImageCommRingCounitIso B S hS X Z).hom.hom.app U ≫
        (directImageCommRingCounitIso B S hS X Z).inv.hom.app U =
      𝟙 ((directInverseDirectStructureSheaf B S hS X Z).obj.obj U) :=
    (NatTrans.comp_app _ _ U).symm.trans
      ((NatTrans.congr_app (ObjectProperty.isoHom_inv_id_hom
        (directImageCommRingCounitIso B S hS X Z)) U).trans (NatTrans.id_app _ U))
  have key : ∀ w : ToType ((directInverseDirectStructureSheaf B S hS X Z).obj.obj U),
      ((directImageCommRingCounitIso B S hS X Z).inv.hom.app U).hom
        (((directImageCommRingCounitIso B S hS X Z).hom.hom.app U).hom w) = w := fun w ↦
    congrArg (fun k : (directInverseDirectStructureSheaf B S hS X Z).obj.obj U ⟶
      (directInverseDirectStructureSheaf B S hS X Z).obj.obj U ↦ k.hom w) hcomp
  exact Eq.trans (key a).symm (Eq.trans (congrArg _ hab) (key b))

/-- **The inverse-image form of the structure map of a closed immersion, pushed forward**, is
`i_*i⁻¹` of the direct-image form followed by the direct image of the counit. -/
theorem directImageStructureSharpInverseImage_eq :
    directImageStructureSharpInverseImage B S hS (subspaceInclusion B S hS X Z) =
      (pushforwardCommRingFunctor (subspaceToposHom B S hS X Z)).map
          ((inverseImageCommRingFunctor (subspaceToposHom B S hS X Z)).map
            (structureSharpCommRing B S hS (subspaceInclusion B S hS X Z))) ≫
        (directImageCommRingCounitIso B S hS X Z).hom := by
  have hfac : structureSharpInverseImage B S hS (subspaceInclusion B S hS X Z) =
      (inverseImageCommRingFunctor (subspaceToposHom B S hS X Z)).map
          (structureSharpCommRing B S hS (subspaceInclusion B S hS X Z)) ≫
        (commRingImageAdjunction (subspaceToposHom B S hS X Z)).counit.app
          (smallEtaleRingedTopos B S hS (subspaceSpace B S hS Z)).O :=
    Adjunction.homEquiv_counit
      (commRingImageAdjunction (subspaceToposHom B S hS X Z)) _ _ _
  refine Eq.trans
    (congrArg (pushforwardCommRingFunctor (subspaceToposHom B S hS X Z)).map hfac) ?_
  exact (pushforwardCommRingFunctor (subspaceToposHom B S hS X Z)).map_comp _ _

/-- **The inverse-image form of the structure map, pushed forward, read on sections.**  It is
the third map of `AlgebraicGeometry.Space.directImageDefiningIdealComplex` followed by the
direct image of the counit. -/
theorem directImageStructureSharpInverseImage_val_app (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (z : ToType ((directImageInverseImageStructureSheaf B S hS
      (subspaceInclusion B S hS X Z)).obj.obj U)) :
    ((directImageStructureSharpInverseImage B S hS
          (subspaceInclusion B S hS X Z)).hom.app U).hom z =
      ((directImageCommRingCounitIso B S hS X Z).hom.hom.app U).hom
        (((directImageDefiningIdealComplex B S hS X Z).g.val.app U).hom z) := by
  refine Eq.trans (congrArg (fun m ↦ (m.hom.app U).hom z)
    (directImageStructureSharpInverseImage_eq B S hS X Z)) ?_
  refine congrArg ((directImageCommRingCounitIso B S hS X Z).hom.hom.app U).hom ?_
  refine Eq.trans (pushforwardInverseImageCommRing_val_app B S hS X Z
    (structureSharpCommRing B S hS (subspaceInclusion B S hS X Z)) U z) ?_
  exact Eq.trans
    (congrArg (fun t ↦ ringDirectInverseSection B S hS X Z t U z)
      (map_structureSharpCommRing B S hS (subspaceInclusion B S hS X Z)))
    (directImageDefiningIdealComplex_g_val_app B S hS X Z U z).symm

/-! ### The kernel of the pushed-forward structure map, presented by `i_*i⁻¹𝓘` -/

/-- **`i_*i⁻¹𝓘`, as a sheaf of modules over `i_*i⁻¹𝒪_X`.**  The direct image along `i` of the
inverse image along `i` of the defining ideal sheaf, taken over the inverse-image sheaf of rings
rather than over `𝒪_X`. -/
noncomputable def directImageInverseImageIdeal :=
  (pushforwardModuleFunctor (subspaceToposHom B S hS X Z)
      (inverseImageRingSheaf (subspaceToposHom B S hS X Z)
        (structureRingSheaf B S hS X))).obj
    ((inverseImageModules (subspaceToposHom B S hS X Z)
        (structureRingSheaf B S hS X)).obj
      (definingIdealSheaf B S hS X Z).toSheafOfModules)

/-- **The sheaf of rings that `i_*i⁻¹𝓘` is a module over is `i_*i⁻¹𝒪_X` itself**, in its two
spellings: the direct image of the inverse-image sheaf of rings, and the sheaf of rings underlying
the sheaf of commutative rings `AlgebraicGeometry.Space.directImageInverseImageStructureSheaf`. -/
theorem ringSheaf_directImageInverseImageStructureSheaf :
    Stacks.SheafOfModules.Tensor.ringSheaf
        (directImageInverseImageStructureSheaf B S hS (subspaceInclusion B S hS X Z)) =
      pushforwardRingSheaf
        (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X Z)).toToposHom
        (inverseImageRingSheaf
          (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X Z)).toToposHom
          (structureRingSheaf B S hS X)) := rfl

/-- **The direct image of the inverse image of the unit module is the unit module.** -/
theorem directInverseUnitModule :
    (pushforwardModuleFunctor (subspaceToposHom B S hS X Z)
          (inverseImageRingSheaf (subspaceToposHom B S hS X Z)
            (structureRingSheaf B S hS X))).obj
        ((inverseImageModules (subspaceToposHom B S hS X Z)
            (structureRingSheaf B S hS X)).obj
          (SheafOfModules.unit (structureRingSheaf B S hS X))) =
      SheafOfModules.unit (pushforwardRingSheaf (subspaceToposHom B S hS X Z)
        (inverseImageRingSheaf (subspaceToposHom B S hS X Z)
          (structureRingSheaf B S hS X))) :=
  Eq.trans
    (congrArg (pushforwardModuleFunctor (subspaceToposHom B S hS X Z)
        (inverseImageRingSheaf (subspaceToposHom B S hS X Z)
          (structureRingSheaf B S hS X))).obj
      (pullbackModuleObj_unit (SmallEtale.topology B S hS (subspaceSpace B S hS Z).1)
        (subspaceToposHom B S hS X Z).inverseImage (structureRingSheaf B S hS X)))
    (pullbackModuleObj_unit (SmallEtale.topology B S hS X.1)
      (subspaceToposHom B S hS X Z).pushforward
      (inverseImageRingSheaf (subspaceToposHom B S hS X Z)
        (structureRingSheaf B S hS X)))

/-- **The inclusion `i_*i⁻¹𝓘 ⟶ i_*i⁻¹𝒪_X`**, as the direct image of the inverse image of the
inclusion of the defining ideal sheaf.  Its target is the unit module of the inverse-image sheaf
of rings by `AlgebraicGeometry.Space.directInverseUnitModule`. -/
noncomputable def directImageInverseImageIdealι :
    directImageInverseImageIdeal B S hS X Z ⟶
      (pushforwardModuleFunctor (subspaceToposHom B S hS X Z)
          (inverseImageRingSheaf (subspaceToposHom B S hS X Z)
            (structureRingSheaf B S hS X))).obj
        ((inverseImageModules (subspaceToposHom B S hS X Z)
            (structureRingSheaf B S hS X)).obj
          (SheafOfModules.unit (structureRingSheaf B S hS X))) :=
  (pushforwardModuleFunctor (subspaceToposHom B S hS X Z)
      (inverseImageRingSheaf (subspaceToposHom B S hS X Z)
        (structureRingSheaf B S hS X))).map
    ((inverseImageModules (subspaceToposHom B S hS X Z)
        (structureRingSheaf B S hS X)).map (definingIdealSheaf B S hS X Z).ι)

/-! ### The presentation of the kernel, sectionwise

The kernel of the split surjection as a family of sections: the inclusion of the sections of
`i_*i⁻¹𝓘` into the sections of `i_*i⁻¹𝒪_X` and the scalar action of `i_*i⁻¹𝒪_X`, followed by
their compatibilities with the split surjection, addition, scalar multiplication and
restriction. -/

/-- **The inclusion `i_*i⁻¹𝓘 ⟶ i_*i⁻¹𝒪_X` on sections**, with values in the sections of
`i_*i⁻¹𝒪_X` read as a sheaf of commutative rings. -/
noncomputable def directImageInverseImageIdealIota (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (y : ToType ((directImageInverseImageIdeal B S hS X Z).val.obj U)) :
    ToType ((directImageInverseImageStructureSheaf B S hS
      (subspaceInclusion B S hS X Z)).obj.obj U) :=
  ((directImageInverseImageIdealι B S hS X Z).val.app U).hom y

/-- The scalar action of a section of `i_*i⁻¹𝒪_X` on a section of `i_*i⁻¹𝓘`. -/
noncomputable def directImageInverseImageIdealSmul (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : ToType ((directImageInverseImageStructureSheaf B S hS
      (subspaceInclusion B S hS X Z)).obj.obj U))
    (y : ToType ((directImageInverseImageIdeal B S hS X Z).val.obj U)) :
    ToType ((directImageInverseImageIdeal B S hS X Z).val.obj U) :=
  (show ToType ((pushforwardRingSheaf (subspaceToposHom B S hS X Z)
    (inverseImageRingSheaf (subspaceToposHom B S hS X Z)
      (structureRingSheaf B S hS X))).obj.obj U) from a) • y

/-- The inclusion on sections is the first map of
`AlgebraicGeometry.Space.directImageDefiningIdealComplex`: restriction of scalars changes
neither the sections nor the map. -/
theorem directImageInverseImageIdealIota_eq (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (y : ToType ((directImageDefiningIdealComplex B S hS X Z).X₁.val.obj U)) :
    directImageInverseImageIdealIota B S hS X Z U y =
      ((directImageDefiningIdealComplex B S hS X Z).f.val.app U).hom y := rfl

/-- **The inclusion is injective on sections.** -/
theorem injective_directImageInverseImageIdealIota (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (y z : ToType ((directImageInverseImageIdeal B S hS X Z).val.obj U))
    (hyz : directImageInverseImageIdealIota B S hS X Z U y =
      directImageInverseImageIdealIota B S hS X Z U z) : y = z :=
  injective_directImageDefiningIdeal_f_val_app B S hS X Z U hyz

/-- **A section killed by the pushed-forward structure map comes from `i_*i⁻¹𝓘`.** -/
theorem exists_directImageInverseImageIdealIota (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : ToType ((directImageInverseImageStructureSheaf B S hS
      (subspaceInclusion B S hS X Z)).obj.obj U))
    (hx : ((directImageStructureSharpInverseImage B S hS
      (subspaceInclusion B S hS X Z)).hom.app U).hom x = 0) :
    ∃ y : ToType ((directImageInverseImageIdeal B S hS X Z).val.obj U),
      directImageInverseImageIdealIota B S hS X Z U y = x := by
  have hzero : ((directImageDefiningIdealComplex B S hS X Z).g.val.app U).hom x = 0 := by
    refine injective_directImageCommRingCounitIso_hom_app B S hS X Z U _ 0 ?_
    refine Eq.trans ?_
      (map_zero ((directImageCommRingCounitIso B S hS X Z).hom.hom.app U).hom).symm
    exact Eq.trans (directImageStructureSharpInverseImage_val_app B S hS X Z U x).symm hx
  obtain ⟨y, hy⟩ := LinearMap.mem_range.1
    (mem_range_directImageDefiningIdeal_f_val_app B S hS X Z U hzero)
  exact ⟨y, Eq.trans (directImageInverseImageIdealIota_eq B S hS X Z U y) hy⟩

/-- **The pushed-forward structure map kills `i_*i⁻¹𝓘`.** -/
theorem directImageInverseImageIdealIota_eq_zero (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (y : ToType ((directImageInverseImageIdeal B S hS X Z).val.obj U)) :
    ((directImageStructureSharpInverseImage B S hS
        (subspaceInclusion B S hS X Z)).hom.app U).hom
      (directImageInverseImageIdealIota B S hS X Z U y) = 0 := by
  have h0 : ((0 : (directImageDefiningIdealComplex B S hS X Z).X₁ ⟶
      (directImageDefiningIdealComplex B S hS X Z).X₃).val.app U).hom y = 0 := rfl
  have hz : ((directImageDefiningIdealComplex B S hS X Z).g.val.app U).hom
      (((directImageDefiningIdealComplex B S hS X Z).f.val.app U).hom y) = 0 :=
    Eq.trans
      (congrArg (fun m ↦ (m.val.app U).hom y)
        (directImageDefiningIdealComplex B S hS X Z).zero)
      h0
  refine Eq.trans (directImageStructureSharpInverseImage_val_app B S hS X Z U
    (directImageInverseImageIdealIota B S hS X Z U y)) ?_
  refine Eq.trans
    (congrArg ((directImageCommRingCounitIso B S hS X Z).hom.hom.app U).hom hz) ?_
  exact map_zero ((directImageCommRingCounitIso B S hS X Z).hom.hom.app U).hom

/-- The inclusion on sections is additive. -/
theorem directImageInverseImageIdealIota_add (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (y z : ToType ((directImageInverseImageIdeal B S hS X Z).val.obj U)) :
    directImageInverseImageIdealIota B S hS X Z U (y + z) =
      directImageInverseImageIdealIota B S hS X Z U y +
        directImageInverseImageIdealIota B S hS X Z U z :=
  map_add ((directImageInverseImageIdealι B S hS X Z).val.app U).hom y z

/-- **The inclusion on sections is semilinear**, the scalar action on the target being the
multiplication of `i_*i⁻¹𝒪_X`. -/
theorem directImageInverseImageIdealIota_smul (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : ToType ((directImageInverseImageStructureSheaf B S hS
      (subspaceInclusion B S hS X Z)).obj.obj U))
    (y : ToType ((directImageInverseImageIdeal B S hS X Z).val.obj U)) :
    directImageInverseImageIdealIota B S hS X Z U
        (directImageInverseImageIdealSmul B S hS X Z U a y) =
      a * directImageInverseImageIdealIota B S hS X Z U y :=
  Eq.trans
    (map_smul ((directImageInverseImageIdealι B S hS X Z).val.app U).hom
      (show ToType ((pushforwardRingSheaf (subspaceToposHom B S hS X Z)
        (inverseImageRingSheaf (subspaceToposHom B S hS X Z)
          (structureRingSheaf B S hS X))).obj.obj U) from a) y)
    (pullbackModuleObj_unit_smul (SmallEtale.topology B S hS X.1)
      (subspaceToposHom B S hS X Z).pushforward
      (inverseImageRingSheaf (subspaceToposHom B S hS X Z) (structureRingSheaf B S hS X)) U _ _)

/-- The inclusion on sections commutes with restriction. -/
theorem directImageInverseImageIdealIota_map {U V : (SmallEtale B S hS X.1)ᵒᵖ} (f : U ⟶ V)
    (y : ToType ((directImageInverseImageIdeal B S hS X Z).val.obj U)) :
    directImageInverseImageIdealIota B S hS X Z V
        ((directImageInverseImageIdeal B S hS X Z).val.map f y) =
      ((directImageInverseImageStructureSheaf B S hS
          (subspaceInclusion B S hS X Z)).obj.map f).hom
        (directImageInverseImageIdealIota B S hS X Z U y) :=
  PresheafOfModules.naturality_apply (directImageInverseImageIdealι B S hS X Z).val f y

end AlgebraicGeometry.Space

end
