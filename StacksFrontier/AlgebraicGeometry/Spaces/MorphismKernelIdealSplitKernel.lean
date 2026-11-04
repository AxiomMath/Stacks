module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageKernelIdealModuleCounit
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismKernelIdealSplitSections

/-!
# The inverse-image form of the structure map, and its kernel, at a free morphism

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`.  `StacksFrontier/AlgebraicGeometry/Spaces/MorphismKernelIdealSplitSections.lean` presents
`f_*f⁻¹𝓘_f` on sections.  This file identifies the **inverse-image form** `f_*(f♯)` of the
structure map, which is the split surjection the derivation of Stacks 02HP runs on, with the
third map of `AlgebraicGeometry.Space.directImageKernelIdealComplex` followed by the direct
image of the counit of `f⁻¹ ⊣ f_*`, and reads the kernel off.

## Main results

* `AlgebraicGeometry.Space.directImageStructureSharpInverseImageOfHom_eq` and
  `…_val_app`: **the pushed-forward inverse-image form of the structure map is `f_*f⁻¹` of the
  direct-image form followed by the direct image of the counit**, as morphisms and on sections.
  Neither needs a hypothesis on `f`.
* `AlgebraicGeometry.Space.directImageInverseImageKernelIdealIota_eq_zero`: the split surjection
  kills `f_*f⁻¹𝓘_f`, at an arbitrary morphism.

## Implementation notes

**`AlgebraicGeometry.RingedToposHom.fSharpInverseImage` is by definition the adjunct of the
direct-image form**, so it is `f⁻¹(f♯)` followed by the counit
(`CategoryTheory.Adjunction.homEquiv_counit`); pushing that forward gives
`directImageStructureSharpInverseImageOfHom_eq`.  No closed immersion is involved: what a closed
immersion buys is that the counit is *invertible*, which is used only where the kernel of the
split surjection is identified with the kernel of `f_*f⁻¹(f♯)`.

**The sections of `f_*f⁻¹` of a homomorphism of sheaves of rings are named.**  Both the
module-level third map of `AlgebraicGeometry.Space.directImageKernelIdealComplex` and the
`CommRingCat`-level `f_*f⁻¹` of the structure map are, on sections,
`AlgebraicGeometry.Space.ringDirectInverseSectionOfHom` at the same homomorphism; routing the
two through that common spelling is what makes the comparison `rfl` at a variable morphism.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map of a
  morphism of algebraic spaces in its two forms.
* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV), the adjunction whose
  counit this is.
* [Stacks Project, Tag 02HP](https://stacks.math.columbia.edu/tag/02HP), the consumer.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- The sections over `U` of the direct image along `f` of the inverse image along `f` of a
sheaf of sets on the small étale site of `Y`. -/
noncomputable abbrev directInverseSectionsOfHom (f : X ⟶ Y)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) : Type u :=
  (Sheaf.sectionsFunctor (SmallEtale.topology B S hS Y.1) U).obj
    ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj
      ((smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.obj G))

/-- The sections over `U` of `f_*f⁻¹` of a homomorphism of sheaves of rings on the small étale
site of `Y` out of the structure sheaf. -/
noncomputable def ringDirectInverseSectionOfHom (f : X ⟶ Y)
    {Rt : Sheaf (SmallEtale.topology B S hS Y.1) RingCat.{u}}
    (t : structureRingSheaf B S hS Y ⟶ Rt)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (z : ToType ((directImageInverseImageStructureSheaf B S hS f).obj.obj U)) :
    directInverseSectionsOfHom B S hS f U (Sheaf.ringSheaf Rt) :=
  (Sheaf.sectionsFunctor (SmallEtale.topology B S hS Y.1) U).map
    ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map
      ((smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.map
        ((sheafCompose (SmallEtale.topology B S hS Y.1) (forget RingCat.{u})).map t))) z

/-- The third map of `AlgebraicGeometry.Space.directImageKernelIdealComplex`, read on sections,
is `f_*f⁻¹` of the `RingCat`-valued structure map. -/
theorem directImageKernelIdealComplex_g_val_app (f : X ⟶ Y)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (z : ToType ((directImageInverseImageStructureSheaf B S hS f).obj.obj U)) :
    ((directImageKernelIdealComplex B S hS f).g.val.app U).hom z =
      ringDirectInverseSectionOfHom B S hS f (structureSharp B S hS f) U z := rfl

/-- `f_*f⁻¹` of a homomorphism of sheaves of *commutative* rings, read on sections, is `f_*f⁻¹`
of the underlying homomorphism of sheaves of rings. -/
theorem pushforwardInverseImageCommRingOfHom_val_app (f : X ⟶ Y)
    (h : (smallEtaleRingedTopos B S hS Y).O ⟶
      (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).obj
        (smallEtaleRingedTopos B S hS X).O)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (z : ToType ((directImageInverseImageStructureSheaf B S hS f).obj.obj U)) :
    ((((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).map
        ((inverseImageCommRingFunctor
          (smallEtaleRingedToposHom B S hS f).toToposHom).map h)).hom.app U).hom) z =
      ringDirectInverseSectionOfHom B S hS f
        ((sheafCompose (SmallEtale.topology B S hS Y.1)
          (forget₂ CommRingCat.{u} RingCat.{u})).map h) U z := by
  have key : (sheafCompose (SmallEtale.topology B S hS Y.1) (forget RingCat.{u})).map
        ((Stacks.forgetCommRingSheaf.{u, u + 1, u} (SmallEtale.topology B S hS Y.1)).map
          ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).map
            ((inverseImageCommRingFunctor
              (smallEtaleRingedToposHom B S hS f).toToposHom).map h))) =
      (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map
        ((smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.map
          ((sheafCompose (SmallEtale.topology B S hS Y.1) (forget RingCat.{u})).map
            ((Stacks.forgetCommRingSheaf.{u, u + 1, u}
              (SmallEtale.topology B S hS Y.1)).map h))) := by
    have e0 : (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).map
          ((inverseImageCommRingFunctor
            (smallEtaleRingedToposHom B S hS f).toToposHom).map h) =
        pullbackCommRingSheafMap (SmallEtale.topology B S hS Y.1)
          (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward
          (pullbackCommRingSheafMap (SmallEtale.topology B S hS X.1)
            (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage h) := rfl
    rw [e0]
    refine Eq.trans (congrArg
      (sheafCompose (SmallEtale.topology B S hS Y.1) (forget RingCat.{u})).map
      (Eq.trans
        (forgetCommRingSheaf_map_pullbackCommRingSheafMap (SmallEtale.topology B S hS Y.1)
          (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward
          (pullbackCommRingSheafMap (SmallEtale.topology B S hS X.1)
            (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage h))
        (congrArg (pullbackRingSheafMap (SmallEtale.topology B S hS Y.1)
            (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward)
          (forgetCommRingSheaf_map_pullbackCommRingSheafMap (SmallEtale.topology B S hS X.1)
            (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage h)))) ?_
    refine Eq.trans (ringSheafMap_pullbackRingSheafMap (SmallEtale.topology B S hS Y.1)
      (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward
      (pullbackRingSheafMap (SmallEtale.topology B S hS X.1)
        (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage
        ((Stacks.forgetCommRingSheaf.{u, u + 1, u}
          (SmallEtale.topology B S hS Y.1)).map h))) ?_
    exact congrArg (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map
      (ringSheafMap_pullbackRingSheafMap (SmallEtale.topology B S hS X.1)
        (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage
        ((Stacks.forgetCommRingSheaf.{u, u + 1, u} (SmallEtale.topology B S hS Y.1)).map h))
  exact congrArg
    (fun m ↦ (Sheaf.sectionsFunctor (SmallEtale.topology B S hS Y.1) U).map m z) key

/-! ### The counit, and the inverse-image form of the structure map on sections -/

/-- `f_*f⁻¹f_*𝒪_X`, the third term of the direct image of the inverse image of the sequence
`𝓘_f ⟶ 𝒪_Y ⟶ f_*𝒪_X`, as a sheaf of commutative rings. -/
noncomputable abbrev directInverseDirectStructureSheafOfHom (f : X ⟶ Y) :
    Sheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u} :=
  (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).obj
    ((inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).obj
      ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).obj
        (smallEtaleRingedTopos B S hS X).O))

/-- **The inverse-image form of the structure map, pushed forward**, is `f_*f⁻¹` of the
direct-image form followed by the direct image of the counit of `f⁻¹ ⊣ f_*`.  No hypothesis on
`f`: this is `CategoryTheory.Adjunction.homEquiv_counit` and functoriality. -/
theorem directImageStructureSharpInverseImageOfHom_eq (f : X ⟶ Y) :
    directImageStructureSharpInverseImage B S hS f =
      (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).map
          ((inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).map
            (structureSharpCommRing B S hS f)) ≫
        (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).map
          ((commRingImageAdjunction
            (smallEtaleRingedToposHom B S hS f).toToposHom).counit.app
              (smallEtaleRingedTopos B S hS X).O) := by
  have hfac : structureSharpInverseImage B S hS f =
      (inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).map
          (structureSharpCommRing B S hS f) ≫
        (commRingImageAdjunction
          (smallEtaleRingedToposHom B S hS f).toToposHom).counit.app
            (smallEtaleRingedTopos B S hS X).O :=
    Adjunction.homEquiv_counit
      (commRingImageAdjunction (smallEtaleRingedToposHom B S hS f).toToposHom) _ _ _
  refine Eq.trans
    (congrArg (pushforwardCommRingFunctor
      (smallEtaleRingedToposHom B S hS f).toToposHom).map hfac) ?_
  exact (pushforwardCommRingFunctor
    (smallEtaleRingedToposHom B S hS f).toToposHom).map_comp _ _

/-- **The inverse-image form of the structure map, pushed forward, read on sections.**  It is
the third map of `AlgebraicGeometry.Space.directImageKernelIdealComplex` followed by the direct
image of the counit.  No hypothesis on `f`. -/
theorem directImageStructureSharpInverseImageOfHom_val_app (f : X ⟶ Y)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (z : ToType ((directImageInverseImageStructureSheaf B S hS f).obj.obj U)) :
    ((directImageStructureSharpInverseImage B S hS f).hom.app U).hom z =
      (((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).map
            ((commRingImageAdjunction
              (smallEtaleRingedToposHom B S hS f).toToposHom).counit.app
                (smallEtaleRingedTopos B S hS X).O)).hom.app U).hom
        (((directImageKernelIdealComplex B S hS f).g.val.app U).hom z) := by
  refine Eq.trans (congrArg (fun m ↦ (m.hom.app U).hom z)
    (directImageStructureSharpInverseImageOfHom_eq B S hS f)) ?_
  refine congrArg (((pushforwardCommRingFunctor
    (smallEtaleRingedToposHom B S hS f).toToposHom).map
      ((commRingImageAdjunction
        (smallEtaleRingedToposHom B S hS f).toToposHom).counit.app
          (smallEtaleRingedTopos B S hS X).O)).hom.app U).hom ?_
  refine Eq.trans (pushforwardInverseImageCommRingOfHom_val_app B S hS f
    (structureSharpCommRing B S hS f) U z) ?_
  exact Eq.trans
    (congrArg (fun t ↦ ringDirectInverseSectionOfHom B S hS f t U z)
      (map_structureSharpCommRing B S hS f))
    (directImageKernelIdealComplex_g_val_app B S hS f U z).symm

/-- **The split surjection of Stacks 02HP kills `f_*f⁻¹𝓘_f`**, at an arbitrary morphism of
algebraic spaces: the third map of
`AlgebraicGeometry.Space.directImageKernelIdealComplex` already kills it, and the direct image
of the counit is additive. -/
theorem directImageInverseImageKernelIdealIota_eq_zero (f : X ⟶ Y)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (y : ToType ((directImageInverseImageKernelIdeal B S hS f).val.obj U)) :
    ((directImageStructureSharpInverseImage B S hS f).hom.app U).hom
      (directImageInverseImageKernelIdealIota B S hS f U y) = 0 := by
  have h0 : ((0 : (directImageKernelIdealComplex B S hS f).X₁ ⟶
      (directImageKernelIdealComplex B S hS f).X₃).val.app U).hom y = 0 := rfl
  have hz : ((directImageKernelIdealComplex B S hS f).g.val.app U).hom
      (((directImageKernelIdealComplex B S hS f).f.val.app U).hom y) = 0 :=
    Eq.trans
      (congrArg (fun m ↦ (m.val.app U).hom y)
        (directImageKernelIdealComplex B S hS f).zero)
      h0
  refine Eq.trans (directImageStructureSharpInverseImageOfHom_val_app B S hS f U
    (directImageInverseImageKernelIdealIota B S hS f U y)) ?_
  refine Eq.trans (congrArg (((pushforwardCommRingFunctor
    (smallEtaleRingedToposHom B S hS f).toToposHom).map
      ((commRingImageAdjunction
        (smallEtaleRingedToposHom B S hS f).toToposHom).counit.app
          (smallEtaleRingedTopos B S hS X).O)).hom.app U).hom hz) ?_
  exact map_zero (((pushforwardCommRingFunctor
    (smallEtaleRingedToposHom B S hS f).toToposHom).map
      ((commRingImageAdjunction
        (smallEtaleRingedToposHom B S hS f).toToposHom).counit.app
          (smallEtaleRingedTopos B S hS X).O)).hom.app U).hom

/-! ### The counit of a closed immersion, and the kernel -/

/-- The direct image along `f` of the counit `f⁻¹f_*𝒪_X ≅ 𝒪_X` of a closed immersion.  This is
the one place closedness enters the presentation of the kernel: `commRingCounitIso` is
Stacks 04E5, part (1), at an arbitrary morphism carrying `IsClosedImmersion`. -/
noncomputable def directImageCommRingCounitIsoOfHom (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) :
    directInverseDirectStructureSheafOfHom B S hS f ≅
      (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).obj
        (smallEtaleRingedTopos B S hS X).O :=
  (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).mapIso
    (commRingCounitIso B S hS f hf (smallEtaleRingedTopos B S hS X).O)

/-- The isomorphism is the direct image of the counit. -/
theorem directImageCommRingCounitIsoOfHom_hom (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) :
    (directImageCommRingCounitIsoOfHom B S hS f hf).hom =
      (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).map
        ((commRingImageAdjunction
          (smallEtaleRingedToposHom B S hS f).toToposHom).counit.app
            (smallEtaleRingedTopos B S hS X).O) := rfl

/-- The direct image of the counit of a closed immersion is injective on sections over every
object.

The inverse law is taken at the *presheaf* level, as the canonical
`CategoryTheory.ObjectProperty.isoHom_inv_id_hom` of the full subcategory `CategoryTheory.Sheaf`
is, and only then read on sections; the `congrArg` lambda is therefore ascribed at a morphism of
the section rings rather than at a morphism of sheaves.  Taking the law at the sheaf level
instead makes the elaborator project `.hom.app U` out of a composite of morphisms of sheaves,
which it can only do by unfolding the two sheaf morphisms themselves, and that exhausts the
heartbeat budget. -/
theorem injective_directImageCommRingCounitIsoOfHom_hom_app (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (a b : ToType ((directInverseDirectStructureSheafOfHom B S hS f).obj.obj U))
    (hab : ((directImageCommRingCounitIsoOfHom B S hS f hf).hom.hom.app U).hom a =
      ((directImageCommRingCounitIsoOfHom B S hS f hf).hom.hom.app U).hom b) : a = b := by
  have hcomp : (directImageCommRingCounitIsoOfHom B S hS f hf).hom.hom.app U ≫
        (directImageCommRingCounitIsoOfHom B S hS f hf).inv.hom.app U =
      𝟙 ((directInverseDirectStructureSheafOfHom B S hS f).obj.obj U) :=
    (NatTrans.comp_app _ _ U).symm.trans
      ((NatTrans.congr_app (ObjectProperty.isoHom_inv_id_hom
        (directImageCommRingCounitIsoOfHom B S hS f hf)) U).trans (NatTrans.id_app _ U))
  have key : ∀ w : ToType ((directInverseDirectStructureSheafOfHom B S hS f).obj.obj U),
      ((directImageCommRingCounitIsoOfHom B S hS f hf).inv.hom.app U).hom
        (((directImageCommRingCounitIsoOfHom B S hS f hf).hom.hom.app U).hom w) = w := fun w ↦
    congrArg (fun k : (directInverseDirectStructureSheafOfHom B S hS f).obj.obj U ⟶
      (directInverseDirectStructureSheafOfHom B S hS f).obj.obj U ↦ k.hom w) hcomp
  exact Eq.trans (key a).symm (Eq.trans (congrArg _ hab) (key b))

/-- **The sections of the middle term are the sections of `f_*f⁻¹𝒪_Y` as a sheaf of rings.**
The underlying sheaf of sets of the inverse image of sheaves of modules is the inverse image of
the underlying sheaf of sets, and the same for the direct image, so the sections of `f_*f⁻¹𝒪_Y`
as an `𝒪_Y`-module over an object of the small étale site of `Y` are *the same type* as its
sections as a sheaf of commutative rings — definitionally, with no transport.

This is the free-morphism form of
`AlgebraicGeometry.Space.directImageDefiningIdealComplex_X₂_val_obj_eq`, and it is what lets a
consumer hand a section of the presheaf of commutative rings `f_*f⁻¹𝒪_Y` to
`AlgebraicGeometry.Space.mem_range_directImageKernelIdeal_f_val_app`. -/
theorem directImageKernelIdealComplex_X₂_val_obj_eq (f : X ⟶ Y)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ) :
    ((directImageKernelIdealComplex B S hS f).X₂.val.obj U : Type u) =
      ToType ((directImageInverseImageStructureSheaf B S hS f).obj.obj U) :=
  rfl

/-- **A section of `f_*f⁻¹𝒪_Y` killed by the third map of
`AlgebraicGeometry.Space.directImageKernelIdealComplex` comes from `f_*f⁻¹𝓘_f`**, at an
arbitrary morphism, with the section read as a section of the sheaf of commutative rings
`f_*f⁻¹𝒪_Y` and the range written as the inclusion on sections of this development.

**The existential is written out as the type of a `have`, and that is what makes this
affordable.**  The sections of `f_*f⁻¹𝒪_Y` occur in the conclusion as the sections of the sheaf
of commutative rings and in `AlgebraicGeometry.Space.directImageKernelIdealComplex` as the
sections of its middle term; the two are the same type definitionally
(`AlgebraicGeometry.Space.directImageKernelIdealComplex_X₂_val_obj_eq`).  Left to the elaborator
— destructuring the value of
`AlgebraicGeometry.Space.mem_range_directImageKernelIdeal_f_val_app` with no expected type, or
naming only the membership and then applying `LinearMap.mem_range` — deciding it is a
`(deterministic) timeout at `isDefEq`` and at `whnf` respectively, at a variable morphism.
Written out, the elaborator has the type on both sides and each of the two steps is cheap. -/
theorem exists_directImageInverseImageKernelIdealIota_of_g_eq_zero (f : X ⟶ Y)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (x : ToType ((directImageInverseImageStructureSheaf B S hS f).obj.obj U))
    (hx : (directImageKernelIdealComplex B S hS f).g.val.app U x = 0) :
    ∃ y : ToType ((directImageInverseImageKernelIdeal B S hS f).val.obj U),
      directImageInverseImageKernelIdealIota B S hS f U y = x := by
  have hex : ∃ y : ToType ((directImageKernelIdealComplex B S hS f).X₁.val.obj U),
      ((directImageKernelIdealComplex B S hS f).f.val.app U).hom y = x :=
    LinearMap.mem_range.1 (mem_range_directImageKernelIdeal_f_val_app B S hS f U hx)
  obtain ⟨y, hy⟩ := hex
  exact ⟨y, Eq.trans (directImageInverseImageKernelIdealIota_eq B S hS f U y) hy⟩

/-- **A section of `f_*f⁻¹𝒪_Y` killed by the split surjection comes from `f_*f⁻¹𝓘_f`**, at an
arbitrary closed immersion.  Together with
`AlgebraicGeometry.Space.injective_directImageInverseImageKernelIdealIota` this says that the
sections of `f_*f⁻¹𝓘_f` are, through the inclusion, *exactly* the kernel of the split
surjection of Stacks 02HP — which is what the derivation of that tag consumes.

The split surjection is the third map of
`AlgebraicGeometry.Space.directImageKernelIdealComplex` followed by the direct image of the
counit; the counit of a closed immersion is invertible, hence injective on sections, so the two
kernels coincide, and the kernel of the third map is `f_*f⁻¹𝓘_f` at an arbitrary morphism by
`AlgebraicGeometry.Space.exists_directImageInverseImageKernelIdealIota_of_g_eq_zero`. -/
theorem exists_directImageInverseImageKernelIdealIota (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (x : ToType ((directImageInverseImageStructureSheaf B S hS f).obj.obj U))
    (hx : ((directImageStructureSharpInverseImage B S hS f).hom.app U).hom x = 0) :
    ∃ y : ToType ((directImageInverseImageKernelIdeal B S hS f).val.obj U),
      directImageInverseImageKernelIdealIota B S hS f U y = x := by
  refine exists_directImageInverseImageKernelIdealIota_of_g_eq_zero B S hS f U x ?_
  refine injective_directImageCommRingCounitIsoOfHom_hom_app B S hS f hf U _ 0 ?_
  refine Eq.trans ?_
    (map_zero ((directImageCommRingCounitIsoOfHom B S hS f hf).hom.hom.app U).hom).symm
  exact Eq.trans (directImageStructureSharpInverseImageOfHom_val_app B S hS f U x).symm hx

end AlgebraicGeometry.Space

end
