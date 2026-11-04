module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedPullbackPerfectGenerator
public import StacksFrontier.AlgebraicGeometry.Perfect.DetectingBoundednessGenerator
public import StacksFrontier.AlgebraicGeometry.Perfect.QcqsPerfectGenerator
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectDetectedByGlobalSectionsFlat
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectObjectCanonical
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDual
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectFibreHomVanishing
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectFromFibres
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.PseudoCoherentByPerfectTwists

/-!
# Relative perfectness detected by the derived global sections of the perfect twists

Let `A` be a ring and let `X` be a scheme separated, of finite presentation and flat over `A`.
Stacks 0GET: an object `K` of `D_QCoh(𝒪_X)` such that `RΓ(X, E ⊗^L K)` is a perfect object of
`D(A)` for every perfect object `E` of `D(𝒪_X)` is `Spec(A)`-perfect.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isRelativelyPerfect_of_isPerfect_derivedGlobalSectionsOver_tensor`:
  **Stacks 0GET.**

## Implementation notes

The proof is the source's. Stacks 0GES (a perfect object of `D(A)` being pseudo-coherent) makes
`K` pseudo-coherent relative to `A`, hence pseudo-coherent, the morphism being flat and locally
of finite presentation (the scheme case of Stacks 0DII, which is the step the source takes with
Stacks 09UU). With a perfect generator `G` of `D_QCoh(𝒪_X)` (Stacks 09IS), perfectness of
`RΓ(X, G^∨ ⊗^L K)` makes the groups `Hom(G⟦-i⟧, K)` vanish for `i ≪ 0`, so `K` is bounded below
by Stacks 0GEQ. The derived fibres of `K` are bounded below by
`AlgebraicGeometry.isLocallyBoundedBelow_derivedPullback_fibre_of_isPerfect`, which is the
source's computation `RHom(Li^*G, Li^*K) = RΓ(X, G^∨ ⊗^L K) ⊗^L_A κ(𝔭)` carried out on `X`.
Stacks 0GEH, implication (2) ⇒ (1), concludes.

Perfectness of `E` is that of Stacks 08CM on the ringed space of `X`, the source's notion, and
`Spec(A)`-perfectness is `AlgebraicGeometry.Scheme.Hom.IsRelativelyPerfect`, Stacks 0DI0 at the
derived tensor product of Stacks 06YU. Of finite presentation is quasi-compact, quasi-separated
and locally of finite presentation; quasi-separatedness follows from separatedness.

## References

* [Stacks Project, Tag 0GET](https://stacks.math.columbia.edu/tag/0GET)
* [Stacks Project, Tag 0GES](https://stacks.math.columbia.edu/tag/0GES)
* [Stacks Project, Tag 0GEH](https://stacks.math.columbia.edu/tag/0GEH)
* [Stacks Project, Tag 0GEQ](https://stacks.math.columbia.edu/tag/0GEQ)
* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.ModuleSections
open Stacks.SheafOfModules
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Cohomology.ProjectionFormulaPerfect.hasSheafifyOpens
  Stacks.Cohomology.ProjectionFormulaPerfect.wEqualsLocallyBijectiveOpens
  Stacks.AssociatedSheaf.abelianModulesRingSheaf

variable {A : Type u} [CommRing A] {X : Scheme.{u}}

/-- An object of `D(𝒪_X)` in `D⁺` is locally bounded below. -/
theorem isLocallyBoundedBelow_of_plus {Y : Scheme.{u}} (E : DerivedCategory Y.Modules)
    (h : (DerivedCategory.TStructure.t (C := Y.Modules)).plus E) :
    RingedSpace.IsLocallyBoundedBelow Y.toRingedSpace E := by
  obtain ⟨d, hd⟩ := h
  intro _
  refine ⟨⊤, trivial, d, fun i hi => Functor.map_isZero _ ?_⟩
  exact E.isZero_of_isGE d i hi

/-- **Stacks 0GET.** Let `A` be a ring and let `X` be a scheme separated, of finite presentation
and flat over `A`, with structure morphism `f : X ⟶ Spec A`. Let `K` be an object of
`D_QCoh(𝒪_X)`. If `RΓ(X, E ⊗^L K)` is a perfect object of `D(A)` for every perfect object `E` of
`D(𝒪_X)`, then `K` is `Spec(A)`-perfect.

`RΓ(X, -)` is the `A`-linear derived global sections `AlgebraicGeometry.derivedGlobalSectionsOver`,
perfectness in `D(A)` is `StacksDraft.Perfect.IsPerfect`, perfectness of `E` is Stacks 08CM on the
ringed space of `X`, and `Spec(A)`-perfectness is
`AlgebraicGeometry.Scheme.Hom.IsRelativelyPerfect` (Stacks 0DI0). Of finite presentation is
`[QuasiCompact f] [LocallyOfFinitePresentation f]` together with quasi-separatedness, which
separatedness implies. -/
@[stacks 0GET]
theorem Scheme.Hom.isRelativelyPerfect_of_isPerfect_derivedGlobalSectionsOver_tensor
    (f : X ⟶ Spec (CommRingCat.of A)) [IsSeparated f] [QuasiCompact f]
    [LocallyOfFinitePresentation f] [Flat f]
    (K : DerivedCategory (StructureSheafModules X.sheaf))
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (StructureSheafModules X.sheaf) i).obj K).IsQuasicoherent)
    (hperf : ∀ E : DerivedCategory (StructureSheafModules X.sheaf),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E →
        StacksDraft.Perfect.IsPerfect
          ((derivedGlobalSectionsOver f).obj (((derivedTensor X.sheaf).obj E).obj K))) :
    f.IsRelativelyPerfect K := by
  have hqc : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hqs : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have hperf' : ∀ E : DerivedCategory (StructureSheafModules X.sheaf),
      (ringedSite X.sheaf).IsPerfect E → StacksDraft.Perfect.IsPerfect
        ((derivedGlobalSectionsOver f).obj (((derivedTensor X.sheaf).obj K).obj E)) := by
    intro E hE
    let := derivedMonoidalStructure X.sheaf
    let := derivedSymmetricStructure X.sheaf
    exact StacksDraft.Perfect.isPerfect_of_iso
      ((derivedGlobalSectionsOver f).mapIso (BraidedCategory.braiding K E))
      (hperf E (Stacks.Cohomology.PerfectComplexes.isPerfect_of_ringedSite X.toRingedSpace E hE))
  obtain ⟨G, hG, hgen⟩ := exists_isPerfect_generator hqc hqs
  have hGdual := isPerfect_derivedDual X.sheaf G hG
  obtain ⟨-, hhom⟩ := eventually_subsingleton_ext_of_derivedGlobalSections_isPerfect_of_flat f
    G K hG hGdual hgen hK fun E hE =>
      exists_isPerfect_mapDerivedCategory_of_isPerfect_derivedGlobalSectionsOver f _ (hperf' E hE)
  have hplus := plus_of_eventually_subsingleton_shiftedHom hqc hqs G K hG hgen hK hhom
  have hpc : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) K :=
    (Scheme.Hom.isPseudoCoherent_iff_of_flat_of_locallyOfFinitePresentation f K).mp
      (isPseudoCoherent_of_derivedGlobalSectionsOver_tensor_isPerfect f K hK fun E hE =>
        StacksDraft.Perfect.isPseudoCoherent_of_isPerfect _ (hperf E hE))
  exact Scheme.Hom.isRelativelyPerfect_of_isLocallyBoundedBelow_of_fibres f K hpc
    (isLocallyBoundedBelow_of_plus K hplus) fun s =>
      isLocallyBoundedBelow_derivedPullback_fibre_of_isPerfect f G K hG hgen hK
        (hperf' _ hGdual) s

end AlgebraicGeometry

end
