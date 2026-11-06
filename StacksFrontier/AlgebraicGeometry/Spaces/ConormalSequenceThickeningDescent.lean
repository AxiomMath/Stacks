module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceMiddleExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceThickeningKernelVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpCompSections

/-!
# Exactness at the middle term of the conormal sequence of a closed subspace

Let `Z ⊂ X` be a closed subspace of an algebraic space over a base `Bb`, with inclusion
`i : Z ⟶ X` and defining ideal sheaf `𝓘 ⊆ 𝒪_X`.
`AlgebraicGeometry.Space.exact_conormalSequence_of_exists_pushforwardDerivation` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceMiddleExactness.lean` reduces exactness of
```
  𝒞_{Z/X} ⟶ i^*Ω_{X/Bb} ⟶ Ω_{Z/Bb}
```
at the middle term to one statement about derivations, its hypothesis `hdesc`: every
`Bb`-derivation `D` of `𝒪_X` with values in `i_*M` which vanishes on every local section of `𝓘`
is the direct image of a `Bb`-derivation of `𝒪_Z` with values in `M`.

**This file discharges `hdesc` for an arbitrary closed subspace, and so proves exactness at the
middle term — the middle clause of [Stacks Project, Tag 05ZA].**

## How

`AlgebraicGeometry.Space.inverseImageQuotientDerivation` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceThickeningKernelVanishing.lean` is `D`,
read as `Stacks.Sites.QuotientDerivation` data through the inverse-image form
`i^♯ : i^{-1}𝒪_X ⟶ 𝒪_Z` of the structure map; its local surjectivity at the inclusion of a
closed subspace is the instance
`AlgebraicGeometry.Space.isLocallySurjective_structureSharpRingInverseImage_subspaceInclusion`.
So `AlgebraicGeometry.Space.descendedDerivation` of
`StacksFrontier/AlgebraicGeometry/Spaces/LiftDifferenceDescent.lean` turns it into a
`Bb`-derivation of `𝒪_Z` with values in `M` as soon as its vanishing on the sections read from
the base is supplied, and two things are then owed: that vanishing, and the identification of
the direct image of the result with `D`.

**The vanishing.**  `Stacks.Sites.QuotientDerivation.descend_eq_zero` wants the derivation datum
to vanish on the image of a morphism of sheaves of rings, and the morphism in question is
`i^{-1}(b^♯)`; the identity
`AlgebraicGeometry.Space.inverseImageDerivationFun_map_structureSharpInverseImageSet_eq_zero`
of `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceInverseImageDerivation.lean` is that
vanishing, stated at the sheaf-of-sets reading of the same morphism, for an arbitrary morphism
of algebraic spaces and with no thickening hypothesis.  The two readings have the same value on
every section, by `AlgebraicGeometry.Space.app_inverseImage_structureSharpRingInverseImage` and
`AlgebraicGeometry.Space.app_inverseImage_structureSharpInverseImage`; that bridge is
`AlgebraicGeometry.Space.inverseImageDerivationFun_map_structureSharpRingInverseImage_eq_zero`
below.  From it the vanishing follows exactly as
`AlgebraicGeometry.Space.descend_restrictedLiftDifferenceData_structureSharpInverseImage_eq_zero`
of `StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftDifferenceBaseVanishingPair.lean`
obtains the same clause for the difference of two lifts: the structure map of the composite
`i ≫ b` factors through the structure map of `i`, by
`AlgebraicGeometry.Space.app_structureSharpInverseImage_comp`, and
`AlgebraicGeometry.Space.structureSharpRingInverseImage_eq_forget₂` reconciles the two
coefficient readings.

**The identification.**  The descended derivation, transposed back along `i^{-1} ⊣ i_*`, is the
transpose of `D`: that is
`AlgebraicGeometry.Space.structureSharpInverseImageSet_comp_derivationHom_descendedDerivation`
below, and it holds because the descent computes the datum on the image of `i^♯`
(`Stacks.Sites.QuotientDerivation.descend_app`), the datum being the transpose by definition.
The direct image of a derivation is built from the direct-image form of the structure map, which
is the unit followed by the direct image of the inverse-image form
(`AlgebraicGeometry.Space.homEquiv_structureSharpInverseImageSet` through
`CategoryTheory.Adjunction.homEquiv_unit`), so the direct image of the descended derivation is
the transpose transposed, which is `D` by
`AlgebraicGeometry.Space.homEquiv_inverseImageDerivationHom`.  No chart comparison enters.

## Main definitions

* `AlgebraicGeometry.Space.conormalDescendedDerivation`: **the descent of `D` to a
  `Bb`-derivation of `𝒪_Z` with values in `M`**, for an arbitrary closed subspace.

## Main results

* `AlgebraicGeometry.Space.inverseImageDerivationFun_map_structureSharpRingInverseImage_eq_zero`:
  the transpose of `D` kills the sections read from the base, at the `RingCat`-valued reading of
  the inverse image of `b^♯`.  Stated for an arbitrary morphism of algebraic spaces.
* `AlgebraicGeometry.Space.descend_inverseImageQuotientDerivation_eq_zero`: **the vanishing on
  the base** for the descent, which is the hypothesis `hzero` of
  `AlgebraicGeometry.Space.descendedDerivation`.
* `AlgebraicGeometry.Space.conormalPushforwardDerivation_conormalDescendedDerivation`: **the
  direct image of the descent is `D`.**
* `AlgebraicGeometry.Space.exists_conormalPushforwardDerivation_eq`: **the hypothesis `hdesc`,
  for an arbitrary closed subspace.**
* `AlgebraicGeometry.Space.exact_conormalSequence`: **Stacks 05ZA, exactness at the middle term
  of the sequence, unconditionally for a closed subspace.**

## What the whole route costs

Every step is at the generality of an arbitrary morphism of algebraic spaces except one, and
that one needs only that `i` is a closed immersion.  The additivity, the Leibniz rule, the
naturality and the vanishing on the base of the transpose are proved for an arbitrary morphism
in `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceInverseImageDerivation.lean`, and so is
the bridge below.  The exception is
`AlgebraicGeometry.Space.inverseImageDerivationFun_eq_zero_of_app_eq_zero`, the vanishing of the
transpose on the sections killed by `i^♯`, and it goes through the fibre-square presentation of
the defining ideal sheaf — `AlgebraicGeometry.Space.isPullback_definingIdealSheaf` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceDefiningIdealFibreSquare.lean` — carried
through the left exact `i^{-1}`, with the invertible counit `i^{-1}i_*𝒪_Z ⟶ 𝒪_Z` of
[Stacks Project, Tag 04E5], part (1), identifying the kernel of `i^{-1}(i^♯)` with the kernel of
`i^♯ : i^{-1}𝒪_X ⟶ 𝒪_Z`.

No chart comparison enters anywhere: nothing relates `AlgebraicGeometry.Space.conormalModule` on
a chart to any scheme-level conormal sheaf, and the re-anchoring that would state such a
comparison does not terminate.  The route above does not need it.

## The tag

[Stacks Project, Tag 05ZA] asserts exactness at `i^*Ω_{X/Bb}` and at `Ω_{Z/Bb}`, and nothing on
the left.  The clause at the right is
`AlgebraicGeometry.Space.epi_pullbackDifferentialsMap_subspaceInclusion`, unconditional for a
closed subspace; the clause at the middle is
`AlgebraicGeometry.Space.exact_conormalSequence` below, now also unconditional for a closed
subspace, and the tag is registered there.  The source's immersion is an arbitrary one, and the
closed immersions this development models are the ones its conormal module is defined for.

What this also earns is that the consumers which carried the clause as `h05ZA` — the statements
of [Stacks Project, Tag 060F], [Stacks Project, Tag 06BE] and [Stacks Project, Tag 06BJ], every
one of which is stated at a universal first-order thickening — no longer carry it.

## References

* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA), the conormal sequence.
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5), part (1), the counit
  of a closed immersion of small étale topoi, which is the one geometric input.
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619), the bijection that
  turns the clause into a statement about derivations.
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the two forms of the
  structure map, whose adjunction is what identifies the descent with `D`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks.Sites Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X X' Bb : AlgebraicSpaces B S hS} (b : X ⟶ Bb)

/-! ### The spelling bridge for the vanishing on the base -/

section Bridge

variable (f : X' ⟶ X) (M : Modules.{u, u} B S hS X'.1 X'.2)
  (D : PresheafOfModulesOfCommRing.Derivation' ((modulePushforward B S hS f).obj M).val
    (structureSharpInverseImage B S hS b).hom)

/-- **The transpose of a derivation kills the sections read from the base**, at the
`RingCat`-valued reading `f^{-1}(b^♯)` of the inverse image of the structure map of
`b : X ⟶ Bb`.

This is
`AlgebraicGeometry.Space.inverseImageDerivationFun_map_structureSharpInverseImageSet_eq_zero`,
which is stated at the sheaf-of-sets reading of the same morphism, carried across by
`AlgebraicGeometry.Space.app_inverseImage_structureSharpRingInverseImage` and
`AlgebraicGeometry.Space.app_inverseImage_structureSharpInverseImage`: the two readings have the
same value on every section.

This is the reading `Stacks.Sites.QuotientDerivation.descend_eq_zero` consumes, and like the
identity it is carried from it, it holds for an arbitrary morphism `f : X' ⟶ X` with no
thickening hypothesis. -/
theorem inverseImageDerivationFun_map_structureSharpRingInverseImage_eq_zero
    (W : (SmallEtale B S hS X'.1)ᵒᵖ)
    (x : ToType (((smallEtaleInverseImageRing B S hS f).obj
      (inverseImageStructureSheaf B S hS b)).obj.obj W)) :
    inverseImageDerivationFun B S hS b f M D W
        (((inverseImageRingFunctor (smallToposMorphismTypeU B S hS f)).map
          (structureSharpRingInverseImage B S hS b)).hom.app W x) = 0 := by
  refine Eq.trans (congrArg (inverseImageDerivationFun B S hS b f M D W)
    ((app_inverseImage_structureSharpRingInverseImage B S hS f b W x).trans
      (app_inverseImage_structureSharpInverseImage B S hS f b W x))) ?_
  exact inverseImageDerivationFun_map_structureSharpInverseImageSet_eq_zero
    B S hS b f M D W x

end Bridge

/-! ### The descent of a vanishing derivation to the small étale site of the subspace -/

section Descent

variable (Z : ClosedSubspaces B S hS X.1)
  (M : Modules.{u, u} B S hS Z.1.toFunctor Z.2.1)
  (D : PresheafOfModulesOfCommRing.Derivation' ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj M).val
    (structureSharpInverseImage B S hS b).hom)
  (hvanish : ∀ (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj U), D.d x.1 = 0)

include hvanish

/-- **The vanishing on the base for the descent of `D`.**  The derivation of `𝒪_Z` that
`AlgebraicGeometry.Space.inverseImageQuotientDerivation` descends to kills every section of
`𝒪_Z` read from `Bb` along `i ≫ b`.

This is the hypothesis `hzero` of `AlgebraicGeometry.Space.descendedDerivation`, and it is
obtained exactly as
`AlgebraicGeometry.Space.descend_restrictedLiftDifferenceData_structureSharpInverseImage_eq_zero`
obtains the same clause for the difference of two lifts: the structure map of the composite
factors through the structure map of `i` by
`AlgebraicGeometry.Space.app_structureSharpInverseImage_comp`, the two coefficient readings of
the inverse-image structure maps agree on sections by
`AlgebraicGeometry.Space.app_inverseImage_structureSharpRingInverseImage` and
`AlgebraicGeometry.Space.structureSharpRingInverseImage_eq_forget₂`, and
`Stacks.Sites.QuotientDerivation.descend_eq_zero` then reduces the vanishing to
`AlgebraicGeometry.Space.inverseImageDerivationFun_map_structureSharpRingInverseImage_eq_zero`
above. -/
theorem descend_inverseImageQuotientDerivation_eq_zero
    (V : (SmallEtale B S hS
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (s : ToType ((inverseImageStructureSheaf B S hS
      (subspaceInclusion B S hS X Z ≫ b)).obj.obj V)) :
    (inverseImageQuotientDerivation B S hS Z b M D hvanish).descend
        ((structureSharpInverseImage B S hS
          (subspaceInclusion B S hS X Z ≫ b)).hom.app V s) = 0 := by
  have harg : (structureSharpInverseImage B S hS
          (subspaceInclusion B S hS X Z ≫ b)).hom.app V s =
      (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z)).hom.app V
        (((inverseImageRingFunctor (smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS X Z))).map
          (structureSharpRingInverseImage B S hS b)).hom.app V
          (((smallEtaleRingedToposHom_compInverseImageRingIso B S hS
              (subspaceInclusion B S hS X Z) b).inv.app
            (smallEtaleRingedTopos B S hS Bb).O).hom.app V s)) := by
    rw [app_structureSharpInverseImage_comp B S hS
        (subspaceInclusion B S hS X Z) b V s,
      app_inverseImage_structureSharpRingInverseImage B S hS
        (subspaceInclusion B S hS X Z) b V
        (((smallEtaleRingedToposHom_compInverseImageRingIso B S hS
            (subspaceInclusion B S hS X Z) b).inv.app
          (smallEtaleRingedTopos B S hS Bb).O).hom.app V s),
      structureSharpRingInverseImage_eq_forget₂ B S hS
        (subspaceInclusion B S hS X Z)]
    rfl
  refine Eq.trans (congrArg
    (fun z : (structureRingSheaf B S hS
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).obj.obj V ↦
      (inverseImageQuotientDerivation B S hS Z b M D hvanish).descend z) harg) ?_
  exact (inverseImageQuotientDerivation B S hS Z b M D hvanish).descend_eq_zero
    ((inverseImageRingFunctor (smallToposMorphismTypeU B S hS
      (subspaceInclusion B S hS X Z))).map (structureSharpRingInverseImage B S hS b))
    _ rfl
    (fun W x ↦ inverseImageDerivationFun_map_structureSharpRingInverseImage_eq_zero
      B S hS b (subspaceInclusion B S hS X Z) M D W x) _

/-- **The descent of `D` to a `Bb`-derivation of `𝒪_Z` with values in `M`.**

`AlgebraicGeometry.Space.inverseImageQuotientDerivation` is `D` as
`Stacks.Sites.QuotientDerivation` data through `i^♯ : i^{-1}𝒪_X ⟶ 𝒪_Z`, whose local
surjectivity is the instance
`AlgebraicGeometry.Space.isLocallySurjective_structureSharpRingInverseImage_subspaceInclusion`,
and `AlgebraicGeometry.Space.descend_inverseImageQuotientDerivation_eq_zero` above is the
vanishing on the base that `AlgebraicGeometry.Space.descendedDerivation` asks for. -/
noncomputable abbrev conormalDescendedDerivation :
    PresheafOfModulesOfCommRing.Derivation' M.val
      (structureSharpInverseImage B S hS (subspaceInclusion B S hS X Z ≫ b)).hom :=
  descendedDerivation B S hS (subspaceInclusion B S hS X Z ≫ b)
    (inverseImageQuotientDerivation B S hS Z b M D hvanish)
    (descend_inverseImageQuotientDerivation_eq_zero B S hS b Z M D hvanish)

/-- **The descent, transposed back along `i^{-1} ⊣ i_*`, is the transpose of `D`.**

The descent computes the derivation datum on the image of `i^♯`, by
`Stacks.Sites.QuotientDerivation.descend_app`, and the datum is by definition the transpose
`AlgebraicGeometry.Space.inverseImageDerivationFun` of `D`; the two coefficient readings of
`i^♯` have the same value on every section, by
`AlgebraicGeometry.Space.structureSharpRingInverseImage_app`. -/
theorem structureSharpInverseImageSet_comp_derivationHom_descendedDerivation :
    structureSharpInverseImageSet B S hS (subspaceInclusion B S hS X Z) ≫
        derivationHom B S hS (subspaceInclusion B S hS X Z ≫ b) M
          (descendedDerivation B S hS (subspaceInclusion B S hS X Z ≫ b)
            (inverseImageQuotientDerivation B S hS Z b M D hvanish)
            (descend_inverseImageQuotientDerivation_eq_zero B S hS b Z M D hvanish)) =
      inverseImageDerivationHom B S hS b (subspaceInclusion B S hS X Z) M D := by
  refine hom_ext_sections fun W a ↦ ?_
  refine Eq.trans ((sectionsFunctor (SmallEtale.topology B S hS
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1) W).map_comp_apply
    (structureSharpInverseImageSet B S hS (subspaceInclusion B S hS X Z))
    (derivationHom B S hS (subspaceInclusion B S hS X Z ≫ b) M _) a) ?_
  refine Eq.trans (congrArg
    (fun z : (structureRingSheaf B S hS
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).obj.obj W ↦
      (inverseImageQuotientDerivation B S hS Z b M D hvanish).descend z)
    (structureSharpRingInverseImage_app B S hS
      (subspaceInclusion B S hS X Z) W a).symm) ?_
  exact (inverseImageQuotientDerivation B S hS Z b M D hvanish).descend_app a

/-- The direct-image derivation hom of the descent of `D` is the derivation hom of `D`. -/
private theorem pushforwardDerivationHom_descendedDerivation :
    pushforwardDerivationHom B S hS (subspaceInclusion B S hS X Z ≫ b) M
      (descendedDerivation B S hS (subspaceInclusion B S hS X Z ≫ b)
        (inverseImageQuotientDerivation B S hS Z b M D hvanish)
        (descend_inverseImageQuotientDerivation_eq_zero B S hS b Z M D hvanish))
      (subspaceInclusion B S hS X Z) =
    derivationHom B S hS b
      ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj M) D := by
  have hsharp : structureSharpSet B S hS (subspaceInclusion B S hS X Z) =
      (smallEtaleRingedToposHom B S hS
          (subspaceInclusion B S hS X Z)).toToposHom.adj.unit.app
          (structureSetSheaf B S hS X) ≫
        (smallEtaleDirectImage B S hS (subspaceInclusion B S hS X Z)).map
          (structureSharpInverseImageSet B S hS (subspaceInclusion B S hS X Z)) :=
    (homEquiv_structureSharpInverseImageSet B S hS
        (subspaceInclusion B S hS X Z)).symm.trans
      (Adjunction.homEquiv_unit
        (adj := (smallEtaleRingedToposHom B S hS
          (subspaceInclusion B S hS X Z)).toToposHom.adj)
        (f := structureSharpInverseImageSet B S hS (subspaceInclusion B S hS X Z)))
  refine Eq.trans (pushforwardDerivationHom_eq B S hS
    (subspaceInclusion B S hS X Z ≫ b) M _ (subspaceInclusion B S hS X Z)) ?_
  refine Eq.trans (congrArg
    (fun m ↦ m ≫ (smallEtaleDirectImage B S hS (subspaceInclusion B S hS X Z)).map
      (derivationHom B S hS (subspaceInclusion B S hS X Z ≫ b) M _)) hsharp) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg
    (fun m ↦ (smallEtaleRingedToposHom B S hS
        (subspaceInclusion B S hS X Z)).toToposHom.adj.unit.app
        (structureSetSheaf B S hS X) ≫ m)
    (((smallEtaleDirectImage B S hS (subspaceInclusion B S hS X Z)).map_comp
        (structureSharpInverseImageSet B S hS (subspaceInclusion B S hS X Z))
        (derivationHom B S hS (subspaceInclusion B S hS X Z ≫ b) M _)).symm.trans
      (congrArg (smallEtaleDirectImage B S hS (subspaceInclusion B S hS X Z)).map
        (structureSharpInverseImageSet_comp_derivationHom_descendedDerivation
          B S hS b Z M D hvanish)))) ?_
  refine Eq.trans (Adjunction.homEquiv_unit
    (adj := (smallEtaleRingedToposHom B S hS
      (subspaceInclusion B S hS X Z)).toToposHom.adj)
    (f := inverseImageDerivationHom B S hS b
      (subspaceInclusion B S hS X Z) M D)).symm ?_
  exact homEquiv_inverseImageDerivationHom B S hS b
    (subspaceInclusion B S hS X Z) M D

/-- **The direct image of the descent of `D` is `D`.**

`AlgebraicGeometry.Space.pushforwardDerivation`, which
`AlgebraicGeometry.Space.conormalPushforwardDerivation` is, is built from the direct-image form
of the structure map of `i`; that form is the unit of `i^{-1} ⊣ i_*` followed by the direct
image of the inverse-image form, by
`AlgebraicGeometry.Space.homEquiv_structureSharpInverseImageSet` read through
`CategoryTheory.Adjunction.homEquiv_unit`.  So the direct image of the descent is the transpose
of
`AlgebraicGeometry.Space.structureSharpInverseImageSet_comp_derivationHom_descendedDerivation`,
which is `D` by `AlgebraicGeometry.Space.homEquiv_inverseImageDerivationHom`. -/
theorem conormalPushforwardDerivation_conormalDescendedDerivation :
    conormalPushforwardDerivation B S hS Z b M
        (descendedDerivation B S hS (subspaceInclusion B S hS X Z ≫ b)
          (inverseImageQuotientDerivation B S hS Z b M D hvanish)
          (descend_inverseImageQuotientDerivation_eq_zero B S hS b Z M D hvanish)) =
      D := by
  apply PresheafOfModulesOfCommRing.Derivation.ext
  ext U t
  exact congrArg
    (fun m : Sheaf.ringSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) ⟶
        Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X)
          ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj M) ↦
      m.hom.app U t)
    (pushforwardDerivationHom_descendedDerivation B S hS b Z M D hvanish)

end Descent

/-! ### Exactness at the middle term -/

section Middle

variable (Z : ClosedSubspaces B S hS X.1)

/-- **The hypothesis `hdesc` of
`AlgebraicGeometry.Space.exact_conormalSequence_of_exists_pushforwardDerivation`, for an
arbitrary closed subspace.**  Every `Bb`-derivation of `𝒪_X` with values in `i_*M` which vanishes
on every local section of the defining ideal sheaf is the direct image of a `Bb`-derivation of
`𝒪_Z` with values in `M`.

The witness is `AlgebraicGeometry.Space.conormalDescendedDerivation` and the identification is
`AlgebraicGeometry.Space.conormalPushforwardDerivation_conormalDescendedDerivation`. -/
theorem exists_conormalPushforwardDerivation_eq
    (M : Modules.{u, u} B S hS Z.1.toFunctor Z.2.1)
    (D : PresheafOfModulesOfCommRing.Derivation' ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj M).val
      (structureSharpInverseImage B S hS b).hom)
    (hvanish : ∀ (U : (SmallEtale B S hS X.1)ᵒᵖ)
      (x : (definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj U), D.d x.1 = 0) :
    ∃ D' : PresheafOfModulesOfCommRing.Derivation' M.val
        (structureSharpInverseImage B S hS (subspaceInclusion B S hS X Z ≫ b)).hom,
      conormalPushforwardDerivation B S hS Z b M D' = D :=
  ⟨conormalDescendedDerivation B S hS b Z M D hvanish,
    conormalPushforwardDerivation_conormalDescendedDerivation B S hS b Z M D hvanish⟩

/-- **Stacks 05ZA, exactness at the middle term, unconditionally for a closed subspace.**  The
short complex `𝒞_{Z/X} ⟶ i^*Ω_{X/Bb} ⟶ Ω_{Z/Bb}` of [Stacks Project, Tag 05ZA] is exact at
`i^*Ω_{X/Bb}`.

This is
`AlgebraicGeometry.Space.exact_conormalSequence_of_exists_pushforwardDerivation`, whose
hypothesis `hdesc` is `AlgebraicGeometry.Space.exists_conormalPushforwardDerivation_eq` above.
Nothing beyond the inclusion `i` being a closed immersion is used: the one step that used to
carry a thickening hypothesis, the vanishing of the transpose of a derivation on the sections
killed by `i^♯` in inverse-image form, is proved for an arbitrary closed subspace in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceThickeningKernelVanishing.lean` from the
fibre-square presentation of the defining ideal sheaf.

Together with `AlgebraicGeometry.Space.epi_pullbackDifferentialsMap_subspaceInclusion`, which is
the clause at the right, this is the whole of 05ZA for the closed immersions this development
models — the source asserts exactness at `i^*Ω_{X/Bb}` and at `Ω_{Z/Bb}` and nothing on the
left. -/
@[stacks 05ZA "exactness at the middle term: the short complex \
`𝒞_{Z/X} ⟶ i^*Ω_{X/Bb} ⟶ Ω_{Z/Bb}` is exact at `i^*Ω_{X/Bb}`, for a closed subspace"]
theorem exact_conormalSequence :
    (ShortComplex.mk _ _
      (conormalSequenceFirstMap_comp_pullbackDifferentialsMap B S hS Z b)).Exact :=
  exact_conormalSequence_of_exists_pushforwardDerivation B S hS Z b
    (exists_conormalPushforwardDerivation_eq B S hS b Z)

end Middle

end AlgebraicGeometry.Space

end
