module

public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.IdealPowerSmul.Cokernel

/-!
# [Stacks, Tag 01YD] and the dévissage of [Stacks, Tag 01YG] on one hypothesis

[Stacks, Tag 01YD] says that a coherent module on a Noetherian scheme whose support is the union
of two closed sets `Z₁ ∪ Z₂` sits in a short exact sequence of coherent modules whose sub is
supported in `Z₁` and whose quotient is supported in `Z₂`. This file proves it in the form
`Stacks.AlgebraicGeometry.DevissageNoetherian.HasSupportSplitting`, the first of the two
reduction steps that the Noetherian induction of [Stacks, Tag 01YF] is stated over.

Consequently [Stacks, Tag 01YF] and [Stacks, Tag 01YG] hold on the *single* remaining
hypothesis `Stacks.AlgebraicGeometry.DevissageNoetherian.HasIrreducibleDevissage`, the
irreducible case of 01YF — steps 3 and 4 of the source's proof, which rest on
[Stacks, Tag 01Y9], [Stacks, Tag 01J3] and [Stacks, Tag 01YE].

## Main results

* `Stacks.AlgebraicGeometry.IdealPowerSmul.hasSupportSplitting`: **[Stacks, Tag 01YD]**.
* `Stacks.AlgebraicGeometry.IdealPowerSmul.isIdealDevissable_of_isCoherent`: **[Stacks, Tag 01YF]
  on the irreducible case alone**.
* `Stacks.AlgebraicGeometry.IdealPowerSmul.property_of_irreducibleDevissage`: **[Stacks, Tag 01YG]
  on the irreducible case alone** — the statement of Tag 01YG verbatim with
  `HasIrreducibleDevissage X` as its only added hypothesis.

## Implementation notes

The splitting is the subsheaf `I₂ ^ n • F` for `I₂` the ideal sheaf of the reduced induced
structure on `Z₂` and `n` the exponent of
`Stacks.AlgebraicGeometry.IdealPowerSmul.exists_supp_idealPowSmul_subset`, which is where
[Stacks, Tag 01Y9] enters. The source takes `I` to be the ideal of the *first* of the two closed
sets and puts the quotient inside it; since `HasSupportSplitting` asks for the sub inside `Z₁`
and both sets are universally quantified, the roles are exchanged here.

Coherence of the quotient is [Stacks, Tag 01BY] (3) in the form
`AlgebraicGeometry.CoherentAbelian.isCoherent_cokernel`, which is already stated for a cokernel
and needs no short complex to be assembled.

`hasSupportSplitting` is the one declaration carrying the 01YD attribute, and is that tag's whole
covering set: it is unconditional, and
`Stacks.AlgebraicGeometry.DevissageNoetherian.HasSupportSplitting` unfolds to
exactly the assertion of 01YD — for every coherent `F` with `supp F = Z₁ ∪ Z₂` a monomorphism
`ι : G ⟶ F` of coherent modules with coherent cokernel, `supp G ⊆ Z₁` and
`supp (cokernel ι) ⊆ Z₂`. Short exactness of `0 → G → F → cokernel ι → 0` is `mono ι` together
with `ShortComplex.exact_of_g_is_cokernel`, as
`Stacks.AlgebraicGeometry.DevissageNoetherian.isIdealDevissable_of_isCoherent` assembles it.

The other two theorems below carry a hypothesis that the statement of Tag 01YG does not have, so
they are left
untagged: the covering-set rule forbids labelling an assertion that does.

## References

* [Stacks Project, Tag 01YD](https://stacks.math.columbia.edu/tag/01YD)
* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
* [Stacks Project, Tag 01YG](https://stacks.math.columbia.edu/tag/01YG)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.DevissageBounded

universe u

namespace Stacks.AlgebraicGeometry.IdealPowerSmul

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

/-- **[Stacks, Tag 01YD].** A coherent module on a Noetherian scheme whose support is the union
of two closed sets sits in a short exact sequence of coherent modules whose sub is supported in
the first and whose quotient is supported in the second. -/
@[stacks 01YD]
theorem hasSupportSplitting (X : Scheme.{u}) [IsNoetherian X] :
    DevissageNoetherian.HasSupportSplitting X := by
  intro F hF Z₁ Z₂ hZ₁ hZ₂ hsupp
  have hFc : F.IsCoherent := hF
  have hFqc : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  let Z : Closeds X := ⟨Z₂, hZ₂⟩
  obtain ⟨n, hn⟩ := exists_supp_idealPowSmul_subset F ⟨Z₁, hZ₁⟩ Z hsupp.le
  have hGc : (idealPowSmulModule (closedIdeal Z) n F).IsCoherent := isCoherent_idealPowSmul _ n F
  refine ⟨_, idealPowSmulHom (closedIdeal Z) n F,
    inferInstanceAs (Mono (idealPowSmul (closedIdeal Z) n F).ι), hGc, ?_, hn, ?_⟩
  · exact AlgebraicGeometry.CoherentAbelian.isCoherent_cokernel _
  · intro x hx
    by_contra hxZ
    refine notMem_supp_cokernel (closedIdeal Z) n F
      (U := ⟨(Z₂ : Set X)ᶜ, hZ₂.isOpen_compl⟩) x hxZ ?_ hx
    intro W hW
    have hemp : W.2.fromSpec ⁻¹' (Z : Set X) = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun p hp ↦ hW (fromSpec_mem W p) hp
    exact (congrArg PrimeSpectrum.vanishingIdeal hemp).trans PrimeSpectrum.vanishingIdeal_empty

/-- **[Stacks, Tag 01YF], on the irreducible case alone.** Every coherent module on a Noetherian
scheme is ideal-dévissable, given the irreducible case of 01YF. The support splitting of
[Stacks, Tag 01YD] is no longer a hypothesis. -/
theorem isIdealDevissable_of_isCoherent {X : Scheme.{u}} [IsNoetherian X]
    (hirr : DevissageNoetherian.HasIrreducibleDevissage X)
    (F : X.Modules) (hF : F.IsCoherent) : IsIdealDevissable F :=
  DevissageNoetherian.isIdealDevissable_of_isCoherent (hasSupportSplitting X) hirr F hF

/-- **[Stacks, Tag 01YG], on the irreducible case of [Stacks, Tag 01YF] alone.** A property of
modules on a Noetherian scheme that holds on the zero module, is stable under extensions of
coherent modules, and holds on the direct image of every quasi-coherent ideal sheaf on every
integral closed subscheme, holds on every coherent module.

This is the statement of Tag 01YG verbatim with the single added hypothesis
`HasIrreducibleDevissage X`. -/
theorem property_of_irreducibleDevissage {X : Scheme.{u}} [IsNoetherian X]
    (hirr : DevissageNoetherian.HasIrreducibleDevissage X)
    (P : X.Modules → Prop)
    (hzero : P (⊤_ X.Modules))
    (hext : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent → P S.X₁ → P S.X₃ → P S.X₂)
    (hideal : ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
      I.toSheafOfModules.IsQuasicoherent →
      P ((Scheme.Modules.pushforward i).obj I.toSheafOfModules)) :
    ∀ F : X.Modules, F.IsCoherent → P F :=
  DevissageNoetherian.property_of_devissageSteps (hasSupportSplitting X) hirr P hzero hext hideal

end Stacks.AlgebraicGeometry.IdealPowerSmul

end
