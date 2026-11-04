module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedStalkCompletionFunctor
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.UniqueExtensionDepth
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import StacksFrontier.RingTheory.AdicCompletion.DepthMinimalPrime

/-!
# The depth of a completed coherent module at a specialization

Let `X` be a locally Noetherian scheme, `ℐ` a quasi-coherent sheaf of ideals, `ℱ` a coherent
`𝒪_X`-module and `x ⤳ y` a specialization of points of `X`, so that `x` is a generalization of
`y` and the local ring `𝒪_{X,x}` is a localization of `𝒪_{X,y}` at the prime
`𝔮 = 𝔪_x ∩ 𝒪_{X,y}`. For a prime `𝔭` of the completed local ring `𝒪_{X,y}^∧` lying over `𝔮` and
*minimal* over `𝔮 𝒪_{X,y}^∧`, this file identifies

  `depth((ℱ_y^∧)_𝔭) = depth(ℱ_x)`,

the depth of the formal stalk of the completion of `ℱ` at `𝔭` with the depth of the stalk of `ℱ`
at `x` over the local ring `𝒪_{X,x}`. This is the step that turns the depth–distance
inequalities of Stacks 0EJ3, which are stated at primes of a completed local ring, into a
statement about the honest stalk at a generalization — the shape in which Stacks 0EJ5 uses them.

## Main results

* `Stacks.Algebraization.completedStalkDepth_completionFunctor_eq_depth_stalk` — the identity
  above.
* `Stacks.Algebraization.one_le_depth_stalk_of_one_le_completedStalkDepth` — its corollary that
  a positive lower bound on the left transfers to the stalk at `x`.
* `Stacks.Algebraization.depth_stalkModuleFunctor_eq_depth_valPresheafStalk` — the depth of the
  stalk read through `Stacks.Algebraization.stalkModuleFunctor` is the depth of the
  abelian-group stalk of `ℱ.val.presheaf` for Mathlib's module structure on it, which is the
  spelling of `AlgebraicGeometry.IsDepthTwoExtension`.

## Implementation notes

The proof composes three inputs from the library.

* `Stacks.Algebraization.completedStalkDepth_completionFunctor_eq_depth_adicCompletion` replaces
  the formal stalk of the completion of `ℱ` by the `ℐ_y`-adic completion of `ℱ_y`.
* `Module.depth_localized_adicCompletion_eq_of_mem_minimalPrimes` — the additivity of depth
  under completion and localization (Stacks 0EHW) together with the vanishing of the fibre term
  at a minimal prime — strips the completion off, leaving `depth((ℱ_y)_𝔮)`.
* `Stacks.ModuleStalkSpecialization.isLocalizedModule_atPrime_stalkSpecializes` (Stacks 0338)
  and `Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes` exhibit `ℱ_x` over
  `𝒪_{X,x}` as *the* localization of `ℱ_y` at `𝔮`, so `Module.depth_eq_of_isLocalizedModule`
  identifies `depth((ℱ_y)_𝔮)` with `depth(ℱ_x)`.

The two spellings of "the stalk as a module over the local ring" have to be reconciled:
`Stacks.Algebraization.stalkModuleFunctor`, in which the completed stalk and its depth are
stated, and `Stacks.ModuleStalkSpecialization.stalkModule`, in which the localization statement
for a specialization is proved. The comparison is
`AlgebraicGeometry.restrictScalarsStalkFunctorIso`, whose target
`Stacks.ModuleSkyscraper.modulesStalkFunctor` carries exactly the `stalkModule` structure on the
nose; `depth_stalkModuleFunctor_eq_depth_stalkModule` and its localized form
`depth_localizedModule_stalkModuleFunctor_eq` record the resulting equalities of depths once, so
that the main proof is a chain of equalities in term mode. Term mode is needed because the
coherent-module type `AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf` is not
type correct at `instances` transparency, so a rewrite whose motive mentions it fails.

A third spelling occurs in the depth clauses of
`AlgebraicGeometry.IsDepthTwoExtension` and of [Stacks, Tag 0EI3]: the abelian-group stalk
`TopCat.Presheaf.stalk (C := Ab) ℱ.val.presheaf x` with Mathlib's instance
`PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier`. That is the
`Stacks.ModuleStalkSpecialization.stalkModule` spelling with
`AlgebraicGeometry.Scheme.Modules.presheaf` unfolded — `stalkModule` *is* that instance — so
`depth_stalkModuleFunctor_eq_depth_valPresheafStalk` is the same equality restated, and no new
transport is needed. It is restated rather than left to the caller because the two sides are not
syntactically equal, so the `stalkModuleFunctor` statements of this directory cannot be rewritten
into the `IsDepthTwoExtension` clauses; the restriction of scalars along
`SemilinearStalk.commStalkIso` that separates the functor spelling from both of the others is
genuine, and is what `depth_stalkModuleFunctor_eq_depth_stalkModule` discharges.

No `stacks` attribute is placed: this is one of the three ingredients of the reduction in
Stacks 0EJ5, not the tag itself.

## References

* [Stacks Project, Tag 0338](https://stacks.math.columbia.edu/tag/0338), the stalk at a
  generalization as a localization.
* [Stacks Project, Tag 0EHW](https://stacks.math.columbia.edu/tag/0EHW), depth under completion
  and localization.
* [Stacks Project, Tag 0EJ5](https://stacks.math.columbia.edu/tag/0EJ5), the consumer.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.ModuleSkyscraper Stacks.ModuleStalkSpecialization

universe u

namespace Stacks.Algebraization

variable {X : Scheme.{u}}

/-! ### Reconciling the two spellings of the stalk as a module -/

/-- The depth of the stalk of an `𝒪_X`-module at `x`, computed in the
`Stacks.Algebraization.stalkModuleFunctor` spelling, agrees with its depth in the
`Stacks.ModuleStalkSpecialization.stalkModule` spelling. The two differ by the restriction of
scalars `AlgebraicGeometry.restrictScalarsStalkFunctorIso`, whose target is the stalk carrying
exactly the `stalkModule` structure. -/
public theorem depth_stalkModuleFunctor_eq_depth_stalkModule (G : X.Modules) (x : X) :
    letI := stalkModule G x
    Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        ((stalkModuleFunctor x).obj G) =
      Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (G.presheaf.stalk x) :=
  let := stalkModule G x
  Module.depth_eq_depth_of_linearEquiv _
    ((AlgebraicGeometry.restrictScalarsStalkFunctorIso x).app G).toLinearEquiv

/-- The same reconciliation after localizing at a prime `q` of `𝒪_{X,x}`: the localizations of
the two spellings of the stalk have the same depth over `(𝒪_{X,x})_q`, because a linear
equivalence localizes (`Module.localizedEquiv`). -/
public theorem depth_localizedModule_stalkModuleFunctor_eq (G : X.Modules) (x : X)
    (q : Ideal (X.presheaf.stalk x)) [q.IsPrime] :
    letI := stalkModule G x
    Module.depth (Localization.AtPrime q) (IsLocalRing.maximalIdeal (Localization.AtPrime q))
        (LocalizedModule q.primeCompl ((stalkModuleFunctor x).obj G)) =
      Module.depth (Localization.AtPrime q) (IsLocalRing.maximalIdeal (Localization.AtPrime q))
        (LocalizedModule q.primeCompl (G.presheaf.stalk x)) :=
  let := stalkModule G x
  Module.depth_eq_depth_of_linearEquiv _
    (Module.localizedEquiv q.primeCompl
      ((AlgebraicGeometry.restrictScalarsStalkFunctorIso x).app G).toLinearEquiv)

/-- The depth of the stalk of an `𝒪_X`-module at `x`, computed in the
`Stacks.Algebraization.stalkModuleFunctor` spelling, agrees with its depth in the spelling of
`AlgebraicGeometry.IsDepthTwoExtension`: the abelian-group stalk of `F.val.presheaf` carrying
Mathlib's module structure over `𝒪_{X,x}`.

That module structure is `Stacks.ModuleStalkSpecialization.stalkModule` with
`AlgebraicGeometry.Scheme.Modules.presheaf` unfolded, so this is
`depth_stalkModuleFunctor_eq_depth_stalkModule` restated; the restatement exists because the two
sides are not syntactically equal and so neither can be rewritten into the other. -/
public theorem depth_stalkModuleFunctor_eq_depth_valPresheafStalk (G : X.Modules) (x : X) :
    letI : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier G.val x
    Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        ((stalkModuleFunctor x).obj G) =
      Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
  depth_stalkModuleFunctor_eq_depth_stalkModule G x

/-! ### The depth at a specialization -/

/-- **The depth of the formal stalk of a completed coherent module at a specialization.** Let `X`
be locally Noetherian, `ℐ` a quasi-coherent sheaf of ideals, `ℱ` a coherent `𝒪_X`-module and
`x ⤳ y` a specialization, so that `𝒪_{X,x}` is the localization of `𝒪_{X,y}` at the prime
`𝔮 = 𝔪_x ∩ 𝒪_{X,y}`. Let `𝔭` be a prime of `𝒪_{X,y}^∧` lying over `𝔮` and minimal over
`𝔮 𝒪_{X,y}^∧`. Then

  `depth((ℱ_y^∧)_𝔭) = depth(ℱ_x)`.

Completion turns the formal stalk into the `ℐ_y`-adic completion of `ℱ_y`, minimality of `𝔭`
makes the fibre term of the additivity formula vanish, leaving `depth((ℱ_y)_𝔮)`, and the stalk
at a generalization is the localization at `𝔮`, which identifies that with the depth of `ℱ_x`
over `𝒪_{X,x}`. -/
public theorem completedStalkDepth_completionFunctor_eq_depth_stalk
    [IsLocallyNoetherian X] (J : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    {x y : X} (h : x ⤳ y) (P : PrimeSpectrum (completedLocalRing J y)) :
    letI : Algebra (X.presheaf.stalk y) (X.presheaf.stalk x) :=
      (X.presheaf.stalkSpecializes h).hom.toAlgebra
    ∀ [P.asIdeal.LiesOver
        ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).under (X.presheaf.stalk y))],
      P.asIdeal ∈
          (((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).under (X.presheaf.stalk y)).map
            (algebraMap (X.presheaf.stalk y) (completedLocalRing J y))).minimalPrimes →
        completedStalkDepth J ((completionFunctor X J).obj F) y P =
          Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
            ((stalkModuleFunctor x).obj F.obj) := by
  let : Algebra (X.presheaf.stalk y) (X.presheaf.stalk x) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  intro hover hP
  let G : X.Modules := F.obj
  let q : Ideal (X.presheaf.stalk y) :=
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).under (X.presheaf.stalk y)
  let := stalkModule G x
  let := stalkModule G y
  let := stalkSpecializesModule G h
  have hqc : G.IsQuasicoherent := isQuasicoherent_coherentModules_obj F
  have hprime : P.asIdeal.IsPrime := P.isPrime
  have hfin := finite_stalkModuleFunctor_coherentModules_obj F y
  have htower : IsScalarTower (X.presheaf.stalk y) (X.presheaf.stalk x)
      (G.presheaf.stalk x) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hringloc : IsLocalization.AtPrime (X.presheaf.stalk x) q :=
    Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes h
  have hmodloc : IsLocalizedModule q.primeCompl (stalkSpecializesₗ G h) :=
    isLocalizedModule_atPrime_stalkSpecializes G h
  refine (completedStalkDepth_completionFunctor_eq_depth_adicCompletion J F y P).trans
    (((Module.depth_localized_adicCompletion_eq_of_mem_minimalPrimes
        (IdealSheafData.stalk J y) q P.asIdeal hP).trans
      ((depth_localizedModule_stalkModuleFunctor_eq G y q).trans ?_)).trans
      (depth_stalkModuleFunctor_eq_depth_stalkModule G x).symm)
  exact Module.depth_eq_of_isLocalizedModule q (Localization.AtPrime q)
    (LocalizedModule q.primeCompl (G.presheaf.stalk y))
    (LocalizedModule.mkLinearMap _ _) inferInstance
    (X.presheaf.stalk x) (G.presheaf.stalk x) (stalkSpecializesₗ G h) hmodloc

/-- **A positive depth of the formal stalk at a minimal prime over a specialization forces a
positive depth of the stalk at the generalization.** This is the form in which the strict
depth–distance inequalities of Stacks 0EJ3 are consumed: they bound
`Stacks.Algebraization.completedStalkDepth` from below, and
`Stacks.Algebraization.completedStalkDepth_completionFunctor_eq_depth_stalk` transports the
bound to `depth(ℱ_x)`. -/
public theorem one_le_depth_stalk_of_one_le_completedStalkDepth
    [IsLocallyNoetherian X] (J : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    {x y : X} (h : x ⤳ y) (P : PrimeSpectrum (completedLocalRing J y)) :
    letI : Algebra (X.presheaf.stalk y) (X.presheaf.stalk x) :=
      (X.presheaf.stalkSpecializes h).hom.toAlgebra
    ∀ [P.asIdeal.LiesOver
        ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).under (X.presheaf.stalk y))],
      P.asIdeal ∈
          (((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).under (X.presheaf.stalk y)).map
            (algebraMap (X.presheaf.stalk y) (completedLocalRing J y))).minimalPrimes →
        1 ≤ completedStalkDepth J ((completionFunctor X J).obj F) y P →
          1 ≤ Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
            ((stalkModuleFunctor x).obj F.obj) := by
  let : Algebra (X.presheaf.stalk y) (X.presheaf.stalk x) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  intro hover hP hone
  exact (completedStalkDepth_completionFunctor_eq_depth_stalk J F h P hP) ▸ hone

end Stacks.Algebraization

end
