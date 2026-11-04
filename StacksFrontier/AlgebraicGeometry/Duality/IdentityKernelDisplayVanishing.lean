module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.BoxDisplay
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.LeftTensorNotation
public import StacksFrontier.AlgebraicGeometry.Duality.IdentityKernelNaturalPullback
public import StacksFrontier.Homology.PseudoCoherent.Ext

/-!
# The negative-degree half of step 1 of the proof of Tag 0G0E

Let `k` be a field, let `X` be smooth and proper over `k`, let `K` be an object of
`D(𝒪_{X ×_k X})` whose Fourier-Mukai functor induces on `D_perf(𝒪_X)` an endofunctor isomorphic
to the identity, and let `ℰ` and `𝒢` be finite locally free `𝒪_X`-modules.  Step 1 of the proof
of [Stacks, Tag 0G0E] runs on the source's *display*

`H^i(X × X, K ⊗^𝐋 (ℰ ⊠ 𝒢)) = H^i(X, R pr_{2,*}(K ⊗^𝐋 (ℰ ⊠ 𝒢))) = H^i(X, Φ_K(ℰ) ⊗^𝐋 𝒢)
  ≅ H^i(X, ℰ ⊗ 𝒢)`,

and concludes from it that the group vanishes for `i < 0`.  **That vanishing is what this file
proves**, in the `Hom`-form of the second term: every morphism from `𝒪_X[0]` into the `i`-th
shift of `R pr_{2,*}(K ⊗^𝐋 (ℰ ⊠ 𝒢)[0])` is zero when `i < 0`.  It is stated for a morphism out
of an arbitrary module in degree zero, not only out of `𝒪_X`: the argument uses nothing about
the source but that it lies in degrees `≤ 0`, and stating it at a variable module is what lets
the t-structure instance be found.

## Main results

* `Stacks.Duality.hom_single_pushforward_kernel_box_eq_zero_of_neg` — **the
  negative-degree vanishing of the source's display**: for `i < 0` every morphism
  `𝒰[0] ⟶ (R pr_{2,*}(K ⊗^𝐋 (ℰ ⊠ 𝒢)[0]))⟦i⟧` is zero, for every `𝒪_X`-module `𝒰` — the case
  `𝒰 = 𝒪_X` being the display's group.

## Implementation notes

*Why the statement is in `Hom`-form rather than as a cohomology group.*  Derived global sections
in degree `i` and morphisms out of the structure sheaf shifted by `i` are the same group, by
`Stacks.SheafOfModules.derivedGlobalSectionsExtEquiv` of
`StacksDraft/Topology/Sheaves/Cohomology/InternalHom/CohomologyAsObtainedFromTheStructureSheaf`
— precisely, of
`StacksFrontier/Topology/Sheaves/Cohomology/InternalHom/CohomologyAsExtOutOfTheStructureSheaf.lean`,
unconditionally and in every degree — so the `Hom`-group below *is*
`H^i(X, R pr_{2,*}(K ⊗^𝐋 (ℰ ⊠ 𝒢)[0]))`.  The `Hom`-form is used because it is what the
vanishing argument produces directly: the chain of isomorphisms moves the *object*, and the
vanishing at the end is orthogonality of the two halves of the t-structure, a statement about
morphisms.

*Why the second term of the display and not the first.*  The first equality of the display is
[Stacks, Tag 0D5W], available unconditionally as
`Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsPushforwardIso` of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/LerayForDerivedSections.lean`, so
the group below is also `H^i(X × X, K ⊗^𝐋 (ℰ ⊠ 𝒢)[0])`; crossing that equality is a change of
the ambient scheme and of the ring the sections are taken over, and nothing in the vanishing
argument needs it.

*The three steps of the argument.*  The display's second equality is
`AlgebraicGeometry.fourierMukaiDisplayIso` of
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/BoxDisplay.lean`, the derived
projection formula at `pr_2` composed with the box comparison.  Its third is `Φ_K ≅ 𝟭` read at
`ℰ[0]`, which is a perfect object because `ℰ` is finite locally free.  The last identification,
`ℰ[0] ⊗^𝐋 𝒢[0] ≅ (ℰ ⊗ 𝒢)[0]`, is `AlgebraicGeometry.nonempty_derivedTensorSingleIso`, whose
K-flatness input is discharged from finite local freeness of `𝒢`.  The vanishing is then
`CategoryTheory.Triangulated.TStructure.zero_of_isLE_of_isGE`: a module placed in degree `0` is
in degrees `≤ 0`, and a module placed in degree `0` and shifted by `i < 0` is in degrees
`≥ -i > 0`.

*What this does not do.*  Step 1 needs this vanishing **and** the nonvanishing of the same group
at the smallest degree where `K` has cohomology, which is where [Stacks, Tag 0FZ0] and box
duality enter.  **Both halves are now assembled**, in
`StacksFrontier/AlgebraicGeometry/Duality/IdentityKernelStepOne.lean`, whose
`Stacks.Duality.isGE_zero_of_representsIdentityOnPerfect` is step 1 under the hypotheses of the
tag and nothing else; this statement is the first of its inputs, carried onto the product by the
derived adjunction in
`StacksFrontier/AlgebraicGeometry/Duality/IdentityKernelBoxVanishing.lean`.  No tag is registered
here.  The hypothesis `hvan` of
`Stacks.Duality.isGE_zero_and_isLE_zero_of_forall_externalTensorProduct_hom_eq_zero` is still not
discharged, and cannot be: it asks for vanishing at *every* nonzero degree, which is stronger than
the source's proof gives.  Step 1 is instead proved by an induction consuming only the bound at
the degree at hand.

*Two spellings of finite local freeness.*  The hypotheses are taken at
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`, which is the spelling [Stacks, Tag 0FZ0]
produces and the one `fourierMukaiDisplayIso` wants, and converted to
`Stacks.FiniteLocallyFree.IsFiniteLocallyFree` by
`Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry` where the perfectness and
the K-flatness statements need it, exactly as in `StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/ProjectionDisplay.lean`.

*The model of the derived categories.*  `CategoryTheory.HasDerivedCategory.standard` is
activated as a local instance at high priority, as in
`StacksFrontier/AlgebraicGeometry/Duality/IdentityFourierMukaiKernel.lean`: `Φ_K` and the display
are available only at that model, and the locally small instances arrive with the imports as
competitors at their default priority.

## References

* [Stacks Project, Tag 0G0E](https://stacks.math.columbia.edu/tag/0G0E)
* [Stacks Project, Tag 0FYQ](https://stacks.math.columbia.edu/tag/0FYQ)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0FZ0](https://stacks.math.columbia.edu/tag/0FZ0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite

universe u

namespace Stacks.Duality

attribute [local instance 100000] HasDerivedCategory.standard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] [IsProper f]

/-- **`R pr_{2,*}(K ⊗^𝐋 (ℰ ⊠ 𝒢)[0]) ≅ (ℰ ⊗ 𝒢)[0]`**, the second, third and fourth terms of the
display of [Stacks, Tag 0G0E] identified: the derived projection formula at `pr_2` against the
box comparison, followed by `Φ_K ≅ 𝟭` at the perfect object `ℰ[0]`, followed by the computation
of the derived tensor product of two modules in degree zero.

The conclusion is `Nonempty` because the isomorphism `Φ_K ≅ 𝟭` is, as in
`Stacks.Duality.RepresentsIdentityOnPerfect`. -/
theorem nonempty_pushforward_kernel_box_iso_single
    (K : DerivedCategory (Limits.pullback f f).Modules) (hΦ : RepresentsIdentityOnPerfect f K)
    (E G : X.Modules)
    (hE : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hG : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G) :
    Nonempty ((dpush (Limits.pullback.snd f f)).obj
        ((dtenLeft (Limits.pullback f f) K).obj
          ((DerivedCategory.singleFunctor (Limits.pullback f f).Modules 0).obj
            (externalTensorProduct f f E G))) ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj
        (Scheme.Modules.tensorObjRingedSpace X E G)) := by
  refine (nonempty_natIso_fourierMukai_of_representsIdentityOnPerfect f K hΦ).elim fun θ => ?_
  refine (AlgebraicGeometry.nonempty_derivedTensorSingleIso X
    (canonicalDerivedTensorProduct X.toRingedSpace.sheaf) E G
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry G).2 hG)).elim
    fun eten => ?_
  exact ⟨fourierMukaiDisplayIso k f f K E G hG ≪≫
    ((derivedTensorProductFunctor X.toRingedSpace.sheaf).mapIso
      (θ.app ⟨(DerivedCategory.singleFunctor X.Modules 0).obj E,
        isPerfect_singleFunctor_of_isFiniteLocallyFree X E
          ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry E).2 hE)⟩)).app _
      ≪≫ eten⟩

/-- **The negative-degree vanishing of the display of [Stacks, Tag 0G0E]**: for `i < 0` every
morphism

`𝒰[0] ⟶ (R pr_{2,*}(K ⊗^𝐋 (ℰ ⊠ 𝒢)[0]))⟦i⟧`

is zero, for an arbitrary `𝒪_X`-module `𝒰`, an arbitrary kernel `K` representing the identity on
perfect complexes, and finite locally free `ℰ` and `𝒢`.  The case the display needs is
`𝒰 = 𝒪_X`, where by
`Stacks.SheafOfModules.derivedGlobalSectionsExtEquiv` that group of morphisms is
`H^i(X, R pr_{2,*}(K ⊗^𝐋 (ℰ ⊠ 𝒢)[0]))`, and by [Stacks, Tag 0D5W] it is
`H^i(X × X, K ⊗^𝐋 (ℰ ⊠ 𝒢)[0])`, the group the source's display computes.

The display identifies the object with `(ℰ ⊗ 𝒢)[0]`, whose `i`-th shift lies in degrees `≥ -i`,
and `-i > 0`; so the morphism vanishes by orthogonality of the two halves of the t-structure of
`D(𝒪_X)`.  This is the half of step 1 of the source's proof that follows from the display; the
other half, the nonvanishing of the same group, is not proved here. -/
theorem hom_single_pushforward_kernel_box_eq_zero_of_neg
    (K : DerivedCategory (Limits.pullback f f).Modules) (hΦ : RepresentsIdentityOnPerfect f K)
    (E G : X.Modules)
    (hE : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hG : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G)
    (U : X.Modules) (i : ℤ) (hi : i < 0)
    (φ : (DerivedCategory.singleFunctor X.Modules 0).obj U ⟶
      ((dpush (Limits.pullback.snd f f)).obj
        ((dtenLeft (Limits.pullback f f) K).obj
          ((DerivedCategory.singleFunctor (Limits.pullback f f).Modules 0).obj
            (externalTensorProduct f f E G))))⟦i⟧) :
    φ = 0 := by
  refine (nonempty_pushforward_kernel_box_iso_single f K hΦ E G hE hG).elim fun e => ?_
  refine zero_of_comp_mono
    ((CategoryTheory.shiftFunctor (DerivedCategory X.Modules) i).map e.hom) ?_
  exact DerivedCategory.TStructure.t.zero_of_isLE_of_isGE _ 0 (-i) (by omega) inferInstance
    (DerivedCategory.TStructure.t.isGE_shift _ 0 i (-i) (by omega))

end Stacks.Duality

end
