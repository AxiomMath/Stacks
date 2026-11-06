module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfLeraySpectralSequence
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorCanonical
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticCohomologyVanishingAtSchemeUniverse
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LqcohSheafFbcFppfHigherDirectImage

/-!
# The Leray spectral sequence for quasi-coherent modules (Stacks 0782)

Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and quasi-separated 1-morphism of algebraic stacks and `ℱ` a
quasi-coherent `𝒪_𝒳`-module.  **Stacks 0782** gives a first quadrant spectral sequence

`E_2^{p,q} = H^p(𝒴, R^q f_{QCoh,*} ℱ) ⇒ H^{p+q}(𝒳, ℱ)`.

The proof is the source's.  The Leray spectral sequence of `f` (**Stacks 0732**,
`AlgebraicGeometry.Stack.exists_fppfLeraySpectralSequence_of_isParasitic`) has
`E_2^{p,q} = H^p(𝒴, R^q f_* ℱ)`.  Each `R^q f_* ℱ` lies in `LQCoh^fbc(𝒪_𝒴)` (**Stacks 0771**
part (4)(b)), so the kernel and cokernel of the coherator counit
`R^q f_{QCoh,*} ℱ = Q(R^q f_* ℱ) ⟶ R^q f_* ℱ` are parasitic (**Stacks 0779** part (2)).  Parasitic
modules have vanishing cohomology (**Stacks 0775** part (1)), so the counit induces an isomorphism
on `H^p`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_quasicoherentLeraySpectralSequence`:
  **Stacks 0782**.

## Implementation notes

Modules have sections in the universe `u` of the schemes.  Cohomology `H^p(𝒳, -)` is the right
derived functor of `Hom(𝒪_𝒳, -)`; its values lie in `AddCommGrpCat.{u + 1}`, the universe of the
morphisms of the fppf site of an algebraic stack, and so does the spectral sequence.  The
auxiliary big étale site that `LQCoh^fbc` is defined against is `B.toBigEtaleSite`, which does
not appear in the statement.

## References

* [Stacks Project, Tag 0782](https://stacks.math.columbia.edu/tag/0782)
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0775](https://stacks.math.columbia.edu/tag/0775)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w d₁ d₂ d₃

attribute [local instance] FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat enoughInjectives_fppfModules

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  [HasDerivedCategory.{d₁} (Stack.fppfModules B S hS 𝒳)]
  [HasDerivedCategory.{d₂} (Stack.fppfModules B S hS 𝒴)]
  [HasDerivedCategory.{d₃} AddCommGrpCat.{u + 1}]

-- Lean v4.35.0: the `HasProducts` searches behind `hasExt_of_enoughInjectives` exceed the default.
set_option synthInstance.maxHeartbeats 400000 in
/-- **Stacks 0782.** Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and quasi-separated 1-morphism of
algebraic stacks and `ℱ` a quasi-coherent `𝒪_𝒳`-module.  There is a spectral sequence with
`E_2^{p,q} = H^p(𝒴, R^q f_{QCoh,*} ℱ)` converging to `H^{p+q}(𝒳, ℱ)`.

The second page is identified for `p, q ≥ 0`, vanishes outside the first quadrant, and the
sequence abuts to `H^n(𝒳, ℱ)`.  Here `R^q f_{QCoh,*}` is
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentHigherDirectImage` (**Stacks 077A**), and
`H^p` is the right derived functor of `Hom(𝒪, -)` on modules at the universe `u` of the schemes,
with values in `AddCommGrpCat.{u + 1}`. -/
@[stacks 0782 "the whole statement, with modules at the module universe u of the schemes; \
  cohomology the right derived functors of Hom(𝒪, -), valued in AddCommGrpCat.{u + 1}"]
theorem exists_quasicoherentLeraySpectralSequence
    (hqc : IsQuasiCompactMorphism B S hS f) (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (F : quasicoherentModules B S hS 𝒳) :
    ∃ E : CohomologicalSpectralSequence AddCommGrpCat.{u + 1} 0,
      (∀ p q : ℕ, Nonempty ((E.page 2 zero_le_two).X ((p : ℤ), (q : ℤ)) ≅
        ((preadditiveCoyoneda.obj (Opposite.op (SheafOfModules.unit _))).rightDerivedPlus
          (p : ℤ)).obj ((quasicoherentInclusion B S hS 𝒴).obj
            ((quasicoherentHigherDirectImage B S hS f q).obj F)))) ∧
      (∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page 2 zero_le_two).X (p, q))) ∧
      SpectralSequence.AbutsTo E (fun n =>
        ((preadditiveCoyoneda.obj (Opposite.op (SheafOfModules.unit _))).rightDerivedPlus n).obj
          ((quasicoherentInclusion B S hS 𝒳).obj F)) := by
  let := enoughInjectives_fppfModules B S hS 𝒴
  have : HasExt.{u + 1} (Stack.fppfModules B S hS 𝒴) := hasExt_of_enoughInjectives.{u + 1} _
  have hL : ∀ q : ℕ, lqcohSheafFbcFppfModules.{u, w, u} B B.toBigEtaleSite
      (BigFppfSite.toBigEtaleSite_cutoff B) S hS 𝒴
      ((fppfModulesHigherDirectImage B S hS f q).obj ((quasicoherentInclusion B S hS 𝒳).obj F)) :=
    lqcohSheafFbcFppfModules_fppfModulesHigherDirectImage B B.toBigEtaleSite
      (BigFppfSite.toBigEtaleSite_cutoff B) S hS f hqc hqs _
      (lqcohSheafFbcFppfModules_quasicoherentInclusion B B.toBigEtaleSite
        (BigFppfSite.toBigEtaleSite_cutoff B) S hS 𝒳 F)
  have hI2 : ∀ q : ℕ, IsParasitic B S hS 𝒴 .fppf
        (kernel ((coheratorAdjunction B S hS 𝒴).counit.app
          (((fppfModulesPushforward B S hS f).rightDerived q).obj
            ((quasicoherentInclusion B S hS 𝒳).obj F)))).val ∧
      IsParasitic B S hS 𝒴 .fppf
        (cokernel ((coheratorAdjunction B S hS 𝒴).counit.app
          (((fppfModulesPushforward B S hS f).rightDerived q).obj
            ((quasicoherentInclusion B S hS 𝒳).obj F)))).val := by
    intro q
    exact isParasitic_kernel_and_cokernel_coheratorAdjunction_counit B S hS 𝒴 B.toBigEtaleSite
      (BigFppfSite.toBigEtaleSite_cutoff B) _ (hL q)
  obtain ⟨E, h1, h2, h3⟩ := exists_fppfLeraySpectralSequence_of_isParasitic B S hS f
    (fppfModulesPullbackPushforwardAdjunction B S hS f)
    (coheratorAdjunction B S hS 𝒴) ((quasicoherentInclusion B S hS 𝒳).obj F)
    (fun N hN i => isZero_fppfModuleCohomology_of_isParasitic_atSchemeUniverse N hN i)
    (fun q => (hI2 q).1) (fun q => (hI2 q).2)
  refine ⟨E, fun p q => ?_, h2, h3⟩
  have e : (quasicoherentHigherDirectImage B S hS f q).obj F =
      (coherator B S hS 𝒴).obj ((fppfModulesHigherDirectImage B S hS f q).obj
        ((quasicoherentInclusion B S hS 𝒳).obj F)) := rfl
  have h := h1 p q
  rw [e, show fppfModulesHigherDirectImage B S hS f q =
    (fppfModulesPushforward B S hS f).rightDerived q from rfl]
  exact h

end AlgebraicGeometry.Stack.AlgebraicStacks
