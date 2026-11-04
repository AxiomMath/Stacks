module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.TensorPowerDifferentialsForms
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.WholeSpaceCosimplicialModule
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalPairFunctor07JG

/-!
# The module `Ω_D` of the pairs of [Stacks, Tag 07JG] is the completed one-forms of `D`

The connection of the pair `...SmallSite.crystalPair` attached to a crystal takes its values in
`...SmallSite.pairForms`, the `p`-adic completion of the divided power differentials of the
envelope of the presentation of the small site; the de Rham complex of
[Stacks, Proposition 60.21.3, Tag 07LG] is built from the completed forms
`(...SmallSite.wholeSpaceDPAlgebra hp).forms S.p a 0`.  In degree one the two are the same module,
by `Crystalline.tensorPowerDifferentialsFormsEquiv`, and the identification carries the
derivation `...SmallSite.pairDerivation` to the universal differential of the forms.

## Main definitions

* `...SmallSite.crystalPairFormsEquiv` — `Ω_D ≃ Ω̂¹_D`, linear over `D`.

## Main results

* `...SmallSite.crystalPairFormsEquiv_pairDerivation` — it carries `d : D → Ω_D` to the universal
  differential `D → Ω̂¹_D`.
-/

@[expose] public section

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open AlgebraicGeometry Crystalline

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp]

/-- The completed forms of `D` are a module over the ring `D` of the pairs of
[Stacks, Tag 07JG]: the two realisations of `D` are the same completion. -/
noncomputable instance crystalPairFormsModule (a : ℕ) :
    Module (pairRing hp) ((wholeSpaceDPAlgebra hp).forms S.p a 0) :=
  inferInstanceAs (Module ((wholeSpaceDPAlgebra hp).completedRing S.p 0)
    ((wholeSpaceDPAlgebra hp).forms S.p a 0))

/-- **The module `Ω_D` of the pairs of [Stacks, Tag 07JG] is the module of completed one-forms
of `D`**, linearly over `D`. -/
noncomputable def crystalPairFormsEquiv :
    pairForms hp ≃ₗ[pairRing hp] (wholeSpaceDPAlgebra hp).forms S.p 1 0 :=
  tensorPowerDifferentialsFormsEquiv (affineSituation S hp)
    (wholeSpacePresentation S hp)
    (wholeSpacePresentation_surjective S hp) 0

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- **The identification `Ω_D ≃ Ω̂¹_D` carries the derivation `d : D → Ω_D` of
[Stacks, Tag 07JA] to the universal differential of the completed forms.** -/
theorem crystalPairFormsEquiv_pairDerivation (a : pairRing hp) :
    crystalPairFormsEquiv hp (pairDerivation hp a) =
      (wholeSpaceDPAlgebra hp).differential S.p 0
        (show (wholeSpaceDPAlgebra hp).completedRing S.p 0 from a) :=
  tensorPowerDifferentialsFormsEquiv_tensorPowerDerivation (affineSituation S hp)
    (wholeSpacePresentation S hp)
    (wholeSpacePresentation_surjective S hp) 0 a

end Crystalline.GlobalCrystallineSituation.SmallSite

end
