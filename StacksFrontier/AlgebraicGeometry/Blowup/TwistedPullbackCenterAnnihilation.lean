module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorUnitSmul
public import StacksFrontier.AlgebraicGeometry.Blowup.DerivedPullbackCenterAnnihilation
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistFlatness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatHomologyComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredComplexSpectralSequence.HypercohomologySpectralSequencePageAnnihilation

/-!
# The annihilation of [Stacks, Tag 0GA0] carried across the twist

[Stacks, Tag 0GA0] annihilates the cohomology sheaves `H^j(Lp^*M̃)` of the derived pullback to
the blowup. The second page of the hypercohomology spectral sequence that the proof of
[Stacks, Tag 0GA1] builds its filtration from is the cohomology of the *twisted* object
`Lp^*M̃ ⊗^𝐋 𝒪_X(q)`, so the annihilation has to be transported along the twist. Two facts do it,
and neither needs anything new about the blowup:

* the twist is invertible, hence flat (`Stacks.Blowup.isFlat_twistingSheaf_reesGrading`), and
  tensoring with a flat sheaf of modules commutes with cohomology
  (`Stacks.DerivedTensor.RingedSite.homologyTensorFlatIso`), so
  `H^j(Lp^*M̃ ⊗^𝐋 𝒪_X(q)) ≅ H^j(Lp^*M̃) ⊗ 𝒪_X(q)` — the derived tensor product of a ringed space
  is the one of its site of opens by definition, so that comparison applies here verbatim;
* the module structure of a tensor product is that of its first factor, so a global function
  killing `H^j(Lp^*M̃)` kills `H^j(Lp^*M̃) ⊗ 𝒪_X(q)`
  (`AlgebraicGeometry.SheafOfModules.globalSectionToEnd_app_sheafTensorRight_eq_zero`).

The flat comparison is stated for a *complex* in the first variable, so the derived pullback is
first replaced by the degreewise pullback `p^*P̃^•` of a K-flat resolution `P^•` of `M`, along
`Stacks.Cohomology.DerivedPullbackOfATilde.derivedPullbackTildeSingleIso` — the same replacement
`Stacks.Blowup.derivedTwistedPullbackIso` makes.

## Main results

* `Stacks.Blowup.twistedHomologyIsoTensorHomology`: **`H^j(Lp^*M̃ ⊗^𝐋 𝒪_X(q)) ≅
  H^j(Lp^*M̃) ⊗ 𝒪_X(q)`.**
* `Stacks.Blowup.exists_pow_le_center_app_homology_twistedDerivedPullback_eq_zero`:
  **[Stacks, Tag 0GA0] for the twisted derived pullback**, in the form `η.app F = 0` that the
  page annihilation of [Stacks, Tag 0GA1] consumes.

## References

* [Stacks Project, Tag 0GA0](https://stacks.math.columbia.edu/tag/0GA0)
* [Stacks Project, Tag 0GA1](https://stacks.math.columbia.edu/tag/0GA1)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedPullbackOfATilde

universe u

namespace Stacks.Blowup

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] (I : Ideal A)

-- `HasDerivedCategory` at the spelling the derived tensor product of a ringed space is stated
-- at: the type is `BlowUpModules I` by `rfl`, but an instance proved at one spelling does not
-- fire at the other. `Stacks.Blowup.hasDerivedCategoryBlowUpModules` already carries that in
-- `TwistFlatness`; its declaration travels with the import but its registration as an instance
-- does not, so it is registered again here rather than restated.
attribute [local instance] hasDerivedCategoryBlowUpModules

-- Likewise for the commutativity of the rings of sections, carried by
-- `Stacks.Blowup.ringSheaf_isMulCommutative` in `DerivedPullbackCenterAnnihilation`.
attribute [local instance] ringSheaf_isMulCommutative

/-- The same commutativity at the second of the two `rfl`-equal spellings of the sheaf of rings
of a ringed space that are in play here: `terminalSectionToEnd` is stated over
`structureSheafRing X`, the tensor product over
`Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf`, and instance search crosses
neither way. -/
local instance ringSheaf_isMulCommutative_underlying
    (X : AlgebraicGeometry.RingedSpace.{u, u}) :
    ∀ U, IsMulCommutative
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj.obj U) :=
  fun U => inferInstanceAs (IsMulCommutative (X.presheaf.obj U))

/-- **`H^j(Lp^*M̃ ⊗^𝐋 𝒪_X(q)) ≅ H^j(Lp^*M̃) ⊗ 𝒪_X(q)`.** The twist is flat, so tensoring with it
commutes with cohomology; the comparison that says so takes a complex in the first variable, so
the derived pullback is replaced by the degreewise pullback of a K-flat resolution `P^•` of `M`
first, and the replacement is undone on the right-hand side. -/
def twistedHomologyIsoTensorHomology (M : ModuleCat.{u} (CommRingCat.of A))
    (P : CochainComplex (ModuleCat.{u} (CommRingCat.of A)) ℤ) (hP : CochainComplex.KFlat.{u, u} P)
    (g : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} (CommRingCat.of A)) 0).obj M)
    (hg : QuasiIso g) (q j : ℤ) :
    (DerivedCategory.homologyFunctor (BlowUpModules I) j).obj
        (((Stacks.Cohomology.TorAmplitude.derTensor (blowUpRingedSpace I)).tensor.obj
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
              (toSpecRingedSpace I)).obj (DerivedCategory.Q.obj (tildeComplex
                ((CochainComplex.singleFunctor (ModuleCat.{u} (CommRingCat.of A)) 0).obj M))))).obj
          (DerivedCategory.Q.obj
            ((CochainComplex.singleFunctor (BlowUpModules I) 0).obj (blowUpTwist I q)))) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((blowUpRingedSpace I)).presheaf, ((blowUpRingedSpace I)).IsSheaf⟩).obj
          ((DerivedCategory.homologyFunctor (BlowUpModules I) j).obj
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
              (toSpecRingedSpace I)).obj (DerivedCategory.Q.obj (tildeComplex
                ((CochainComplex.singleFunctor (ModuleCat.{u} (CommRingCat.of A))
                  0).obj M)))))).obj
        (blowUpTwist I q) :=
  (DerivedCategory.homologyFunctor (BlowUpModules I) j).mapIso
      (((Stacks.Cohomology.TorAmplitude.derTensor (blowUpRingedSpace I)).tensor.mapIso
        (derivedPullbackTildeSingleIso (toSpecRingedSpace I) M P hP g hg)).app _) ≪≫
    Stacks.DerivedTensor.RingedSite.homologyTensorFlatIso (blowUpRingedSpace I).sheaf
      (blowUpTwist I q) (isFlat_twistingSheaf_reesGrading I q) (pullbackTildeComplex I P) j ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((blowUpRingedSpace I)).presheaf, ((blowUpRingedSpace I)).IsSheaf⟩).flip.obj
        (blowUpTwist I q)).mapIso
      (((DerivedCategory.homologyFunctorFactors (BlowUpModules I) j).app
            (pullbackTildeComplex I P)).symm ≪≫
        ((DerivedCategory.homologyFunctor (BlowUpModules I) j).mapIso
          (derivedPullbackTildeSingleIso (toSpecRingedSpace I) M P hP g hg)).symm)

/-- **[Stacks, Tag 0GA0] for the twisted derived pullback, as the vanishing of a central
endomorphism.** There is a `c > 0`, depending only on `A` and `I`, such that for every
`A`-module `M`, every `j ≤ -t`, every twist `q` and every `r ∈ Iᶜ`, multiplication by the global
section of the blowup attached to `r` is the zero endomorphism of `H^j(Lp^*M̃ ⊗^𝐋 𝒪_X(q))`.

This is `Stacks.Blowup.exists_pow_le_center_app_homology_derivedPullback_eq_zero` carried across
`Stacks.Blowup.twistedHomologyIsoTensorHomology`: the scalar kills the first factor of the
tensor product, hence the tensor product. -/
theorem exists_pow_le_center_app_homology_twistedDerivedPullback_eq_zero [IsNoetherianRing A]
    {n : ℕ} (g : Fin (n + 1) → A) (hI : I = Ideal.span (Set.range g)) :
    ∃ c : ℕ, 0 < c ∧ ∀ (M : ModuleCat.{u} (CommRingCat.of A))
      (P : CochainComplex (ModuleCat.{u} (CommRingCat.of A)) ℤ),
      CochainComplex.KFlat.{u, u} P →
      ∀ (gres : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} (CommRingCat.of A)) 0).obj M),
      QuasiIso gres → ∀ q j : ℤ, j ≤ -((n : ℤ) + 1) → ∀ r ∈ I ^ c,
        (Stacks.SheafOfModules.terminalSectionToEnd
            (structureSheafRing (blowUpSpec I).toRingedSpace) ⊤ isTerminalTop
            ((toSpec I).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv r))).app
          ((DerivedCategory.homologyFunctor (BlowUpModules I) j).obj
            (((Stacks.Cohomology.TorAmplitude.derTensor (blowUpRingedSpace I)).tensor.obj
                ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
                  (toSpecRingedSpace I)).obj (DerivedCategory.Q.obj (tildeComplex
                    ((CochainComplex.singleFunctor (ModuleCat.{u} (CommRingCat.of A))
                      0).obj M))))).obj
              (DerivedCategory.Q.obj
                ((CochainComplex.singleFunctor (BlowUpModules I) 0).obj (blowUpTwist I q)))))
          = 0 := by
  obtain ⟨c, hc, hann⟩ := exists_pow_le_center_app_homology_derivedPullback_eq_zero g I hI
  refine ⟨c, hc, fun M P hP gres hg q j hj r hr => ?_⟩
  refine CategoryTheory.CatCenter.app_eq_zero_of_iso _
    (twistedHomologyIsoTensorHomology I M P hP gres hg q j) ?_
  exact AlgebraicGeometry.SheafOfModules.globalSectionToEnd_app_sheafTensorRight_eq_zero
    (blowUpRingedSpace I).sheaf (blowUpTwist I q) _ _ (hann M j hj r hr)

end Stacks.Blowup

end
