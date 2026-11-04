module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.DerivedStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparison

/-!
# Equation 48.8.0.1: the comparison map at the structure sheaf

Let `f : X ⟶ Y` be a morphism of schemes and let `a` be a right adjoint of the restricted derived
direct image `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. Evaluating the two-variable comparison map of
`Stacks.Duality.compareWithPullbackTensor` at `L = 𝒪_Y` and composing with `a` applied to the
right unitor gives the map displayed in [Stacks, Tag 0A9S],

  `Lf^*K ⊗ᴸ_{𝒪_X} a(𝒪_Y) ⟶ a(K)`,

functorial in `K`.

## Main definitions

All in the namespace `Stacks.Duality`.

* `compareWithPullback` — the map displayed in [Stacks, Tag 0A9S].
* `twistedInverseImageCompareWithPullback` — the same map for the twisted inverse image `f^×` of
  `Stacks.Duality.twistedInverseImage` and its own adjunction.

## Main results

* `compareWithPullback_naturality` — the map is functorial in `K`.

## Implementation notes

*The right unitor is a hypothesis.* The derived tensor product of this repository carries no
unit: `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct` has fields for the tensor and its
comparison maps and none for a unit, so there is no unitor to invoke and none can be unfolded
from the definitions. The isomorphism of functors `ρ`, sending `K` to `K ⊗ᴸ_{𝒪_Y} 𝒪_Y ≅ K`, is
therefore an explicit argument. Taking it as an isomorphism of functors rather than a family of
isomorphisms is what makes `compareWithPullback_naturality` follow from naturality of the
two-variable map.

The unit object itself is not hypothesised: it is
`Stacks.Duality.derivedStructureSheaf`, the structure sheaf placed in degree zero as an object of
`D_QCoh(𝒪_Y)`.

*Why this is a separate module.* Adding the import of
`Stacks.Duality.derivedStructureSheaf` to
`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointPushforward/PullbackComparison.lean` enlarges
the instance search enough to push the elaboration of `Stacks.Duality.projectionFormulaMap` over
the default heartbeat limit. Keeping the specialization in its own module leaves that file's
elaboration environment as it stands, which is the alternative to raising the limit.

## References

* [Stacks Project, Tag 0A9S](https://stacks.math.columbia.edu/tag/0A9S)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Duality.DerivedPushforward

universe u

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  (α : quasiCoherentDerivedTensorSwap Y ⋙ quasiCoherentDerivedPullback' f ⟶
      (quasiCoherentDerivedPullback' f).prod (quasiCoherentDerivedPullback' f) ⋙
        quasiCoherentDerivedTensorSwap X)

section

variable [∀ (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y),
    IsIso (projectionFormulaMap f hpush α E K)]
  {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
  (adj : quasiCoherentDerivedPushforward f hpush ⊣ a)
  (ρ : (quasiCoherentDerivedTensor Y).flip.obj (derivedStructureSheaf Y) ≅ 𝟭 _)

/-- **Equation 48.8.0.1 of [Stacks, Tag 0A9S]**: the comparison map
`Lf^*K ⊗ᴸ_{𝒪_X} a(𝒪_Y) ⟶ a(K)`, the two-variable comparison map at `L = 𝒪_Y` followed by `a`
applied to the right unitor `K ⊗ᴸ_{𝒪_Y} 𝒪_Y ≅ K`. -/
@[stacks 0A9S "variant: the map for an arbitrary cotensorator α, right adjoint a and unitor ρ; \
  the tag is Stacks.Duality.qcqsCompareWithPullback"]
def compareWithPullback (K : quasiCoherentDerivedCategory Y) :
    ((quasiCoherentDerivedTensor X).obj
        ((quasiCoherentDerivedPullback' f).obj K)).obj
        (a.obj (derivedStructureSheaf Y)) ⟶
      a.obj K :=
  compareWithPullbackTensor f hpush α adj K (derivedStructureSheaf Y) ≫
    a.map (ρ.hom.app K)

/-- Equation 48.8.0.1 is functorial in `K`. -/
@[stacks 0A9S "variant: functoriality in K for an arbitrary α, a and ρ; the tag is \
  Stacks.Duality.qcqsCompareWithPullback"]
theorem compareWithPullback_naturality {K K' : quasiCoherentDerivedCategory Y} (h : K ⟶ K') :
    ((quasiCoherentDerivedTensor X).map
          ((quasiCoherentDerivedPullback' f).map h)).app
          (a.obj (derivedStructureSheaf Y)) ≫
        compareWithPullback f hpush α adj ρ K' =
      compareWithPullback f hpush α adj ρ K ≫ a.map h := by
  have hρ : ((quasiCoherentDerivedTensor Y).map h).app (derivedStructureSheaf Y) ≫
      ρ.hom.app K' = ρ.hom.app K ≫ h := ρ.hom.naturality h
  have hnat := compareWithPullbackTensor_naturality_left f hpush α adj h
    (derivedStructureSheaf Y)
  show ((quasiCoherentDerivedTensor X).map
        ((quasiCoherentDerivedPullback' f).map h)).app
        (a.obj (derivedStructureSheaf Y)) ≫
      (compareWithPullbackTensor f hpush α adj K' (derivedStructureSheaf Y) ≫
        a.map (ρ.hom.app K')) =
    (compareWithPullbackTensor f hpush α adj K (derivedStructureSheaf Y) ≫
      a.map (ρ.hom.app K)) ≫ a.map h
  calc ((quasiCoherentDerivedTensor X).map
          ((quasiCoherentDerivedPullback' f).map h)).app
          (a.obj (derivedStructureSheaf Y)) ≫
        (compareWithPullbackTensor f hpush α adj K' (derivedStructureSheaf Y) ≫
          a.map (ρ.hom.app K'))
      = (((quasiCoherentDerivedTensor X).map
            ((quasiCoherentDerivedPullback' f).map h)).app
            (a.obj (derivedStructureSheaf Y)) ≫
          compareWithPullbackTensor f hpush α adj K' (derivedStructureSheaf Y)) ≫
        a.map (ρ.hom.app K') := (Category.assoc _ _ _).symm
    _ = (compareWithPullbackTensor f hpush α adj K (derivedStructureSheaf Y) ≫
          a.map (((quasiCoherentDerivedTensor Y).map h).app (derivedStructureSheaf Y))) ≫
        a.map (ρ.hom.app K') :=
      congrArg (fun z => z ≫ a.map (ρ.hom.app K')) hnat
    _ = compareWithPullbackTensor f hpush α adj K (derivedStructureSheaf Y) ≫
        (a.map (((quasiCoherentDerivedTensor Y).map h).app (derivedStructureSheaf Y)) ≫
          a.map (ρ.hom.app K')) := Category.assoc _ _ _
    _ = compareWithPullbackTensor f hpush α adj K (derivedStructureSheaf Y) ≫
        a.map (((quasiCoherentDerivedTensor Y).map h).app (derivedStructureSheaf Y) ≫
          ρ.hom.app K') :=
      congrArg
        (fun z => compareWithPullbackTensor f hpush α adj K (derivedStructureSheaf Y) ≫ z)
        (a.map_comp _ _).symm
    _ = compareWithPullbackTensor f hpush α adj K (derivedStructureSheaf Y) ≫
        a.map (ρ.hom.app K ≫ h) :=
      congrArg
        (fun z => compareWithPullbackTensor f hpush α adj K
          (derivedStructureSheaf Y) ≫ a.map z) hρ
    _ = compareWithPullbackTensor f hpush α adj K (derivedStructureSheaf Y) ≫
        (a.map (ρ.hom.app K) ≫ a.map h) :=
      congrArg
        (fun z => compareWithPullbackTensor f hpush α adj K (derivedStructureSheaf Y) ≫ z)
        (a.map_comp _ _)
    _ = (compareWithPullbackTensor f hpush α adj K (derivedStructureSheaf Y) ≫
          a.map (ρ.hom.app K)) ≫ a.map h := (Category.assoc _ _ _).symm

end

section TwistedInverseImage

variable [∀ (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y),
    IsIso (projectionFormulaMap f hpush α E K)]
  [(quasiCoherentDerivedPushforward f hpush).IsLeftAdjoint]

/-- **Equation 48.8.0.1 for the twisted inverse image `f^×`** of
`Stacks.Duality.twistedInverseImage`: the comparison map `Lf^*K ⊗ᴸ_{𝒪_X} f^×𝒪_Y ⟶ f^×K` of
[Stacks, Tag 0A9S]. -/
@[stacks 0A9S "variant: the map at a = f^× for an arbitrary α and ρ; the tag is \
  Stacks.Duality.qcqsCompareWithPullback"]
def twistedInverseImageCompareWithPullback
    (ρ : (quasiCoherentDerivedTensor Y).flip.obj (derivedStructureSheaf Y) ≅ 𝟭 _)
    (K : quasiCoherentDerivedCategory Y) :
    ((quasiCoherentDerivedTensor X).obj
        ((quasiCoherentDerivedPullback' f).obj K)).obj
        ((twistedInverseImage f hpush).obj (derivedStructureSheaf Y)) ⟶
      (twistedInverseImage f hpush).obj K :=
  compareWithPullback f hpush α (twistedInverseImageAdjunction f hpush) ρ K

end TwistedInverseImage

end Stacks.Duality

end
