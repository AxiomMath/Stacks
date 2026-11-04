module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.CanonicalMap
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Sheaf
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.SectionGenerator
public import StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Local
public import StacksFrontier.AlgebraicGeometry.AmpleFromAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.PicSurjectiveOpen.AffineGenerator

/-!
# A spanning section of an invertible module trivialises it on an affine open

The proof of clause 3 of [Stacks, Tag 0B3V] works on an affine open `U` carrying a section of
`ℰ` whose image generates `𝓛` there.
`Stacks.ProjectiveBundleConormal.exists_affine_open_splitting_span` produces that open together
with the generator, as the bare statement that the generator spans `Γ(𝓛, U)`; the untwisting of
the source of the conormal map,
`Stacks.ProjectiveBundleConormal.restrictSourceIso`, consumes a *trivialisation*
`𝓛|_U ≅ 𝟙_`. This file is the passage from the first to the second.

## Main definitions

* `Stacks.ProjectiveBundleConormal.restrictIsoUnitOfSpanEqTop`: **a section of an invertible
  module spanning its sections on an affine open trivialises it there**, in the shape
  `(Scheme.Modules.restrictFunctor U.ι).obj L ≅ 𝟙_ _` that `restrictSourceIso` reads.

## Implementation notes

**Affineness is not decoration.** Over a non-affine open the statement is false: on `X = 𝐏¹_k`
with `L = 𝒪(-1)` and `U = ⊤` the module of sections `Γ(L, ⊤)` is zero, so the span of the zero
section is `⊤` vacuously while `L` is not trivial. What affineness buys is that the stalk of a
quasi-coherent module at a point of `U` is a localisation of `Γ(L, U)`, so that a section
spanning `Γ(L, U)` has a germ generating every stalk; that step is
`Stacks.PicSurjectiveOpen.exists_smul_germ_eq_of_surjective_smul`, which asks only for
surjectivity of `c ↦ c • t` and is therefore exactly what the span hypothesis supplies.
Quasi-coherence of `L` itself is the instance
`Stacks.SheafOfModules.Scheme.isQuasicoherent_of_isInvertible`.

**Nothing else is proved here.** Given the germs, the generation of the sections over *every*
open inside `U` is
`Stacks.SheafOfModules.bijective_smul_of_forall_germ_notMem_maximalIdeal_smul_top`, and the
trivialisation on the localised site is `Stacks.SheafOfModules.isoUnitOver`. The germ condition
itself is read off from invertibility by
`Stacks.SheafOfModules.maximalIdeal_smul_top_ne_top_of_isInvertible`: a generator of a stalk not
killed by the maximal ideal cannot lie in `𝔪_y L_y`.

**The two invertibility classes are crossed once**, here and nowhere else below: the hypothesis
is `AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L`, the spelling
the projective-bundle material uses, and the single `have` at the head of the proof turns it
into `Stacks.SheafOfModules.IsInvertible X.presheaf (structureSheafRing X).property L`, the
spelling of the trivialisation API, by
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`.

**`over` versus `restrictFunctor`.** `isoUnitOver` trivialises `L.over U`, the module read on
the localised site `Over U`, whereas the conormal material restricts along the open immersion.
The passage is
`Stacks.AlgebraicGeometry.TwistMapsInvertible.restrictIsoUnitOfOverIsoUnit`; no comparison is
built here. Its target, `SheafOfModules.unit U.toScheme.ringCatSheaf`, is the unit of the
re-seated monoidal structure `Stacks.ProjectiveBundleConormal.monoidalSheafTensor`
definitionally, so the conclusion is ascribed to `𝟙_ _` with no unit comparison.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.ProjectiveBundleConormal

attribute [local instance] monoidalSheafTensor

variable {X : Scheme.{u}}

/-- **A section spanning the sections of an invertible module on an affine open trivialises it
there.** If `t : Γ(L, U)` spans `Γ(L, U)` over `Γ(X, U)` and `U` is affine, then `L|_U` is
isomorphic to the structure sheaf of `U`, in the `restrictFunctor` spelling and at the monoidal
unit of `Stacks.ProjectiveBundleConormal.monoidalSheafTensor`.

Together with `Stacks.ProjectiveBundleConormal.exists_affine_open_splitting_span`, which produces
such a `U` and such a `t` around every point, this is the trivialisation that
`Stacks.ProjectiveBundleConormal.restrictSourceIso` consumes.

The affineness hypothesis cannot be dropped: see the implementation notes of this file. -/
def restrictIsoUnitOfSpanEqTop (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (U : X.Opens) (hU : IsAffineOpen U) (t : Γ(L, U))
    (ht : Submodule.span Γ(X, U) {t} = ⊤) :
    (Scheme.Modules.restrictFunctor U.ι).obj L ≅ 𝟙_ _ := by
  haveI : ∀ z : X.toRingedSpace.carrier, IsLocalRing (ringStalk X.toRingedSpace z) :=
    fun z => inferInstance
  haveI : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L).2 inferInstance
  have hsurj : Function.Surjective fun c : Γ(X, U) => c • t := fun m =>
    Submodule.mem_span_singleton.1 (ht ▸ Submodule.mem_top (x := m))
  refine Stacks.AlgebraicGeometry.TwistMapsInvertible.restrictIsoUnitOfOverIsoUnit L U
    (Stacks.SheafOfModules.isoUnitOver (X := X.toRingedSpace) L U t (fun V hVU => ?_))
  refine Stacks.SheafOfModules.bijective_smul_of_forall_germ_notMem_maximalIdeal_smul_top
    L t V hVU (fun y hy => ?_)
  have hinst := Stacks.SheafOfModules.stalkModule_eq X.toRingedSpace L.val y
  have hproper := Stacks.SheafOfModules.maximalIdeal_smul_top_ne_top_of_isInvertible
    (X := X.toRingedSpace) L y
  rw [hinst]
  let : Module (ringStalk X.toRingedSpace y) (grpStalk X.toRingedSpace L.val y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.toRingedSpace.presheaf) L.val y
  intro hmem
  refine hproper ((Stacks.SheafOfModules.maximalIdeal_smul_top_eq_top_iff_of_module_eq
      (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace L.val y) _
      hinst).mpr (le_antisymm le_top fun z _ => ?_))
  obtain ⟨c, hc⟩ := Stacks.PicSurjectiveOpen.exists_smul_germ_eq_of_surjective_smul
    L hU t hsurj (hVU hy) z
  rw [hc]
  exact Submodule.smul_mem _ c hmem

end Stacks.ProjectiveBundleConormal

end
