module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.FormalFunctionsPseudoCoherent
import all StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.FormalFunctionsPseudoCoherent

/-!
# The theorem on formal functions for a pseudo-coherent complex, on the module side

Let `X` be a locally Noetherian scheme, `𝓘 ⊂ 𝒪_X` a quasi-coherent sheaf of ideals and `K` a
pseudo-coherent object of `D(𝒪_X)`. For an affine open `U ⊂ X`, with `A = Γ(X, U)` and
`I = 𝓘(U)`, [Stacks, Tag 0A0L] asserts
`H^p(U, K^∧) = lim H^p(U, K)/IⁿH^p(U, K) = H^p(U, K)^∧`.
`Completion/FormalFunctionsPseudoCoherent.lean` proves the two equalities for an arbitrary left
adjoint to the inclusion of the derived-complete objects of `D(A)`; this file produces such an
adjoint and states the equalities without assuming one.

## Main results

* `Stacks.Algebraization.exists_derivedCompletionAdjunction`: the inclusion of the
  derived-complete objects of `D(A)` has a left adjoint, for any ideal of a Noetherian ring.
* `Stacks.Algebraization.homology_derivedCompletion_derivedSections_iso_adicCompletion`: the
  first equality on the module side, `H^p(RΓ(U, K)^∧) = lim H^p(U, K)/IⁿH^p(U, K)`, its left hand
  side read at the derived completion in `D(A)` of `RΓ(U, K)`.
* `exists_adjunction_and_adicCompletion_homology_derivedSections_iso_derivedCompletion`: the
  second equality, `lim H^p(U, K)/IⁿH^p(U, K) = H^p(U, K)^∧`.
* `exists_adjunction_and_homology_derivedSections_derivedCompletion_iso_adicCompletion`: the
  transport of the first equality along the identification `RΓ(U, K^∧) = RΓ(U, K)^∧` of [Stacks,
  Tag 0CQI], which takes that identification as an input and so carries no tag itself. It is the
  engine of `Stacks.Algebraization.exists_iso_homology_derivedSections_derivedCompletion_whole`
  of `Completion/FormalFunctionsPseudoCoherentWhole.lean`, where the input is discharged and the
  whole of [Stacks, Tag 0A0L] is registered.

## Implementation notes

Derived completion of `A`-modules is a left adjoint `C` to the inclusion of the derived-complete
objects of `D(A)`, as in [Stacks, Tag 0A06]. It is *produced, not assumed*: each statement below
is a conjunction whose first half exhibits such a `C` — `A = Γ(X, U)` is Noetherian,
so `I = 𝓘(U)` is finitely generated and [Stacks, Tag 0920] applies, which is
`Stacks.Algebraization.exists_derivedCompletionAdjunction` — and whose second half holds for
every such `C`, so that no choice of reflector enters and neither statement is contingent on the
existence of one.

*What of the first equality is registered here, and where the rest is.* The registered form
below reads the left hand side on the module side, at the derived completion in `D(A)` of
`RΓ(U, K)`, rather than at `RΓ(U, K^∧)`. The single step of the source's proof that passes
between the two is the identification `RΓ(U, K^∧) = RΓ(U, K)^∧` of [Stacks, Tag 0CQI], and
`exists_adjunction_and_homology_derivedSections_derivedCompletion_iso_adicCompletion` below is the
transport along it, keeping it as an input.

That input is available in full, and is discharged in
`Completion/FormalFunctionsPseudoCoherentWhole.lean`, whose
`Stacks.Algebraization.exists_iso_homology_derivedSections_derivedCompletion_whole` states both
equalities of the tag at `H^p(U, K^∧)` and carries [Stacks, Tag 0A0L]. Three results make it so,
and the account in `Completion/FormalFunctionsPseudoCoherent.lean` — that the step could not be
discharged at the tag's generality — is out of date:

* [Stacks, Tag 0CQI] is proved at a sheaf of ideals of finite type, for an arbitrary object of
  `D(𝒪)`, as `AlgebraicGeometry.RingedSite.nonempty_iso_derivedSectionsOverObject_derivedCompletion`
  of `DerivedCompletionRinged/LocalCalculationFiniteType.lean`; the nilpotent regime of
  `DerivedCompletionRinged/LocalCalculation.lean` is no longer the only one.
* A quasi-coherent sheaf of ideals of a locally Noetherian scheme **is** of finite type,
  `Stacks.Algebraization.isFiniteType_idealSheafSiteSubmodule`, so the reflector of [Stacks,
  Tag 099F] exists along this tag's own `𝓘` and `K^∧` can be formed; and
  `Stacks.Algebraization.exists_eq_idealOfGlobalSections_overIdeal_affine` supplies [Stacks,
  Tag 0CQI]'s generation hypothesis at an affine open, with the generated ideal equal to `𝓘(U)`
  itself, so the module-side completion is along the tag's own `I = 𝓘(U)`.
* `Stacks.Algebraization.derivedSectionsOverSiteIso` identifies the two models of `RΓ(U, -)` the
  two tags are stated in — the one here and the ringed-site
  `AlgebraicGeometry.RingedSite.derivedSectionsOverObject` — which is what lets the one be fed to
  the other.

## References

* [Stacks Project, Tag 0A0L](https://stacks.math.columbia.edu/tag/0A0L)
* [Stacks Project, Tag 0A06](https://stacks.math.columbia.edu/tag/0A06)
* [Stacks Project, Tag 0920](https://stacks.math.columbia.edu/tag/0920)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
* [Stacks Project, Tag 0CQI](https://stacks.math.columbia.edu/tag/0CQI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.Cohomology.HypercohomologyEdge

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Algebraization

/-! ### The derived completion of `A`-modules exists -/

/-- **The inclusion of the derived-complete objects of `D(A)` has a left adjoint**, for every
ideal `I` of a Noetherian ring `A`.

This is [Stacks, Tag 0920] — derived completion is the derived limit of the tensor–Koszul tower
of a finite generating family — made available without a generating family: an ideal of a
Noetherian ring is finitely generated, and the conclusion does not mention the family. -/
public theorem exists_derivedCompletionAdjunction (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) :
    ∃ C : DerivedCategory (ModuleCat.{u} A) ⥤
        (show ObjectProperty (DerivedCategory (ModuleCat.{u} A)) from
          fun L ↦ IsDerivedComplete I L).FullSubcategory,
      Nonempty (C ⊣ (show ObjectProperty (DerivedCategory (ModuleCat.{u} A)) from
        fun L ↦ IsDerivedComplete I L).ι) := by
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp I.fg_of_isNoetherianRing
  change Ideal.span (Set.range f) = I at hf
  subst I
  obtain ⟨L, hL, _⟩ := AdicKoszulAdjunction.koszulPowerDerivedLimit_isLeftAdjoint A f
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct (ULift.{u} A))
  exact ⟨L, hL⟩

/-! ### The two equalities of the theorem on formal functions, the reflector produced -/

/-- The inclusion of the derived-complete objects of `D(Γ(X, U))` along `𝓘(U)` has a left
adjoint, for `X` locally Noetherian and `U` affine open. -/
private theorem exists_derivedCompletionAdjunction_ideal (X : Scheme.{u}) [IsLocallyNoetherian X]
    (𝓘 : X.IdealSheafData) (U : X.affineOpens) :
    ∃ C : DerivedCategory (ModuleCat.{u} Γ(X, U.1)) ⥤
        (show ObjectProperty (DerivedCategory (ModuleCat.{u} Γ(X, U.1))) from
          fun L ↦ IsDerivedComplete (𝓘.ideal U) L).FullSubcategory,
      Nonempty (C ⊣ (show ObjectProperty (DerivedCategory (ModuleCat.{u} Γ(X, U.1))) from
        fun L ↦ IsDerivedComplete (𝓘.ideal U) L).ι) :=
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  exists_derivedCompletionAdjunction Γ(X, U.1) (𝓘.ideal U)

/-- **Stacks Project, Tag 0A0L, the first equality, read on the module side.** Let `X` be a
locally Noetherian scheme, `𝓘 ⊂ 𝒪_X` a quasi-coherent sheaf of ideals and `K` a pseudo-coherent
object of `D(𝒪_X)`. For an affine open `U`, with `A = Γ(X, U)` and `I = 𝓘(U)`, the degree-`p`
cohomology of the derived completion in `D(A)` of `RΓ(U, K)` is the `I`-adic completion
`lim H^p(U, K)/IⁿH^p(U, K)` of `H^p(U, K)`.

Everything the source's first equality needs beyond the identification `RΓ(U, K^∧)
= RΓ(U, K)^∧`: `A` is Noetherian and `H^n(U, K)` is a finite `A`-module in every degree
(`Stacks.Algebraization.finite_homology_derivedSections_of_isPseudoCoherent`, which is where
pseudo-coherence and the locally Noetherian hypothesis of the tag are used), so [Stacks,
Tag 0A06] applies to `RΓ(U, K)` along `I = 𝓘(U)`.

The derived completion of `A`-modules is produced, not assumed: the first conjunct exhibits a
left adjoint `C` to the inclusion of the derived-complete objects of `D(A)`, by
`Stacks.Algebraization.exists_derivedCompletionAdjunction`, and the second conjunct holds for
every such `C`, so no choice of reflector enters.

The left hand side is the cohomology of `C(RΓ(U, K))`, not of `RΓ(U, K^∧)`; passing between the
two is [Stacks, Tag 0CQI], which
`exists_adjunction_and_homology_derivedSections_derivedCompletion_iso_adicCompletion` below takes
as an input and
`Stacks.Algebraization.exists_iso_homology_derivedSections_derivedCompletion_whole` of
`Completion/FormalFunctionsPseudoCoherentWhole.lean` discharges. -/
@[stacks 0A0L "the first equality `H^p(RΓ(U, K)^∧) = lim H^p(U, K)/IⁿH^p(U, K)` on the module \
side: its left hand side read at the derived completion in `D(A)` of the derived sections \
`RΓ(U, K)`, for `A = Γ(X, U)` and `I = 𝓘(U)`, which is [Stacks, Tag 0A06] applied to `RΓ(U, K)` \
together with the finiteness of the `H^n(U, K)`; the second equality is \
`exists_adjunction_and_adicCompletion_homology_derivedSections_iso_derivedCompletion`"]
public theorem homology_derivedCompletion_derivedSections_iso_adicCompletion
    (X : Scheme.{u}) [IsLocallyNoetherian X] (𝓘 : X.IdealSheafData)
    (K : DerivedCategory X.Modules)
    (hK : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) K)
    (U : X.affineOpens) (p : ℤ) :
    let P : ObjectProperty (DerivedCategory (ModuleCat.{u} Γ(X, U.1))) :=
      fun L ↦ IsDerivedComplete (𝓘.ideal U) L
    (∃ C : DerivedCategory (ModuleCat.{u} Γ(X, U.1)) ⥤ P.FullSubcategory,
        Nonempty (C ⊣ P.ι)) ∧
      ∀ C : DerivedCategory (ModuleCat.{u} Γ(X, U.1)) ⥤ P.FullSubcategory, (C ⊣ P.ι) →
        Nonempty
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) p).obj
              ((C ⋙ P.ι).obj
                ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj K)) ≅
            ModuleCat.of Γ(X, U.1) (AdicCompletion (𝓘.ideal U)
              ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) p).obj
                ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj K)))) := by
  intro P
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  refine ⟨exists_derivedCompletionAdjunction_ideal X 𝓘 U, ?_⟩
  intro C adj
  exact AdicCompletionCohomology.derivedCompletion_homology_iso_adicCompletion
    Γ(X, U.1) (𝓘.ideal U) ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj K)
    (fun n ↦ finite_homology_derivedSections_of_isPseudoCoherent X K hK U n) C adj p

/-- Transport of
`Stacks.Algebraization.homology_derivedCompletion_derivedSections_iso_adicCompletion`
along the identification of [Stacks, Tag 0CQI]: if the derived sections over `U` of an object `Kc`
are the derived completion in `D(A)` of `RΓ(U, K)`, then `H^p(U, Kc)` is the `I`-adic completion
of `H^p(U, K)`.

This carries no tag of its own, `Kc` and the identification `RΓ(U, Kc) ≅ RΓ(U, K)^∧` being
inputs. It is the engine that turns the module-side first equality into the source's
`H^p(U, K^∧) = lim H^p(U, K)/IⁿH^p(U, K)` once `Kc` is known to be `K^∧`, and that is carried out
in `Completion/FormalFunctionsPseudoCoherentWhole.lean`: the identification is [Stacks, Tag 0CQI]
at a sheaf of ideals of finite type, which a quasi-coherent sheaf of ideals of a locally
Noetherian scheme is. Granted the input, nothing else about `K^∧` is used here. See the module
note. -/
public theorem exists_adjunction_and_homology_derivedSections_derivedCompletion_iso_adicCompletion
    (X : Scheme.{u}) [IsLocallyNoetherian X] (𝓘 : X.IdealSheafData)
    (K Kc : DerivedCategory X.Modules)
    (hK : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) K)
    (U : X.affineOpens) (p : ℤ) :
    let P : ObjectProperty (DerivedCategory (ModuleCat.{u} Γ(X, U.1))) :=
      fun L ↦ IsDerivedComplete (𝓘.ideal U) L
    (∃ C : DerivedCategory (ModuleCat.{u} Γ(X, U.1)) ⥤ P.FullSubcategory,
        Nonempty (C ⊣ P.ι)) ∧
      ∀ C : DerivedCategory (ModuleCat.{u} Γ(X, U.1)) ⥤ P.FullSubcategory, (C ⊣ P.ι) →
        Nonempty
          ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj Kc ≅
            (C ⋙ P.ι).obj
              ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj K)) →
        Nonempty
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) p).obj
              ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj Kc) ≅
            ModuleCat.of Γ(X, U.1) (AdicCompletion (𝓘.ideal U)
              ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) p).obj
                ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj K)))) := by
  intro P
  refine ⟨exists_derivedCompletionAdjunction_ideal X 𝓘 U, ?_⟩
  intro C adj hCQI
  obtain ⟨eCQI⟩ := hCQI
  obtain ⟨-, h⟩ := homology_derivedCompletion_derivedSections_iso_adicCompletion X 𝓘 K hK U p
  obtain ⟨e⟩ := h C adj
  exact ⟨(DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) p).mapIso eCQI ≪≫ e⟩

/-- **Stacks Project, Tag 0A0L, the second equality.** With the notation of
`homology_derivedCompletion_derivedSections_iso_adicCompletion`, the `I`-adic completion
`lim H^p(U, K)/IⁿH^p(U, K)` of `H^p(U, K)` is the derived `I`-adic completion of the `A`-module
`H^p(U, K)`, read in degree zero.

This is [Stacks, Tag 0A06] for the complex `H^p(U, K)[0]`, which is legitimate because
`H^p(U, K)` is a finite module. Nothing is assumed: the first conjunct produces the derived
completion of `A`-modules — a left adjoint `C` to the inclusion of the derived-complete objects
of `D(A)`, by `Stacks.Algebraization.exists_derivedCompletionAdjunction` — and the second holds
for every such `C`. -/
public theorem exists_adjunction_and_adicCompletion_homology_derivedSections_iso_derivedCompletion
    (X : Scheme.{u}) [IsLocallyNoetherian X] (𝓘 : X.IdealSheafData)
    (K : DerivedCategory X.Modules)
    (hK : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) K)
    (U : X.affineOpens) (p : ℤ) :
    let P : ObjectProperty (DerivedCategory (ModuleCat.{u} Γ(X, U.1))) :=
      fun L ↦ IsDerivedComplete (𝓘.ideal U) L
    (∃ C : DerivedCategory (ModuleCat.{u} Γ(X, U.1)) ⥤ P.FullSubcategory,
        Nonempty (C ⊣ P.ι)) ∧
      ∀ C : DerivedCategory (ModuleCat.{u} Γ(X, U.1)) ⥤ P.FullSubcategory, (C ⊣ P.ι) →
        Nonempty
          (ModuleCat.of Γ(X, U.1) (AdicCompletion (𝓘.ideal U)
              ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) p).obj
                ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj K))) ≅
            (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) 0).obj
              ((C ⋙ P.ι).obj
                ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U.1)) 0).obj
                  ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) p).obj
                    ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj K))))) := by
  intro P
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  refine ⟨exists_derivedCompletionAdjunction_ideal X 𝓘 U, ?_⟩
  intro C adj
  have hfin := finite_homology_derivedSections_of_isPseudoCoherent X K hK U p
  obtain ⟨e⟩ := AdicCompletionCohomology.derivedCompletion_homology_iso_adicCompletion
    Γ(X, U.1) (𝓘.ideal U)
    ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U.1)) 0).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) p).obj
        ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj K)))
    (fun n ↦ finite_homology_single_of_finite _ n) C adj 0
  exact ⟨(e ≪≫ ((AdicCompletion.congr (𝓘.ideal U)
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} Γ(X, U.1))
      0).app _).toLinearEquiv).restrictScalars Γ(X, U.1)).toModuleIso).symm⟩

end Stacks.Algebraization

end
