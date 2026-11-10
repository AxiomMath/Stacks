module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumSequence
import all StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumSequence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The sequence of Tag 0C4T with its kernel inclusion named

`Stacks.Divisors.addEffectiveCartierDivisor_shortExact` asserts that the short exact sequence
`0 ⟶ 𝒪_X(-D)|_C ⟶ 𝒪_{C+D} ⟶ 𝒪_D ⟶ 0` of [Stacks, Tag 0C4T] exists, with its kernel inclusion
bound by an existential quantifier. This file names that inclusion and characterises it, so that
equations about it can be stated.

## Main results

* `Stacks.Divisors.sumKernelMap`: the kernel inclusion as a named morphism.
* `Stacks.Divisors.unit_comp_sumKernelMap` and `Stacks.Divisors.eq_sumKernelMap`: the equation
  that characterises it, and the uniqueness that equation gives.
* `Stacks.Divisors.shortExact_sumKernelMap`: [Stacks, Tag 0C4T] asserted about the named morphism.

## References

* [Stacks Project, Tag 0C4T](https://stacks.math.columbia.edu/tag/0C4T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
  TopologicalSpace

open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Divisors

/-- **Nested kernels of compatible quotient sequences.** Given two exact sequences with the same
middle term mapping onto two quotients, a morphism of the quotients compatible with them induces
a short exact sequence of the kernels. The statement is phrased in the opposite category, so
that it is applied to quotient sequences and produces the sequence of their kernels.

The induced morphism is reported together with the equation that *characterises* it,
`g ≫ R.f = S.f ≫ a.inv ≫ T.g ≫ b.hom`. Since `R.f` is a monomorphism that equation pins `g`
down uniquely, so a caller can name its own morphism, check the equation, and inherit short
exactness for it. Without the equation the morphism is anonymous and nothing downstream can
state a compatibility about it. -/
private theorem shortExact_kernels_of_shortExact_quotients_with_comp
    {C : Type*} [Category* C] [Abelian C]
    (S T R : ShortComplex C) (hS : S.Exact) (hT : T.ShortExact)
    (hR : R.Exact) [Mono S.f] [Mono R.f]
    (a : T.X₂ ≅ S.X₂) (b : T.X₃ ≅ R.X₂) (c : S.X₃ ≅ R.X₃)
    (h : T.g ≫ b.hom ≫ R.g = a.hom ≫ S.g ≫ c.hom)
    (f : T.X₁ ⟶ S.X₁) (hf : f ≫ S.f = T.f ≫ a.hom) :
    ∃ (g : S.X₁ ⟶ R.X₁) (hz : f ≫ g = 0),
      (ShortComplex.mk f g hz).ShortExact ∧
        g ≫ R.f = S.f ≫ a.inv ≫ T.g ≫ b.hom := by
  have := hT.mono_f
  have := hT.epi_g
  have hz : (S.f ≫ a.inv ≫ T.g ≫ b.hom) ≫ R.g = 0 := by
    simp only [Category.assoc, h, Iso.inv_hom_id_assoc, S.zero_assoc, zero_comp]
  let g := hR.lift (S.f ≫ a.inv ≫ T.g ≫ b.hom) hz
  have hg : g ≫ R.f = S.f ≫ a.inv ≫ T.g ≫ b.hom := hR.lift_f _ hz
  have hfg : f ≫ g = 0 := by
    apply (cancel_mono R.f).1
    simp [Category.assoc, hg, ← Category.assoc f S.f, hf, T.zero_assoc]
  have : Mono f := mono_of_mono_fac hf
  have hker : IsLimit (KernelFork.ofι f hfg) := by
    apply KernelFork.IsLimit.ofι'
    intro W k hk
    have hk' : (k ≫ S.f ≫ a.inv) ≫ T.g = 0 := by
      apply (cancel_mono b.hom).1
      simp [Category.assoc, ← hg, ← Category.assoc k g, hk]
    refine ⟨hT.exact.lift (k ≫ S.f ≫ a.inv) hk', ?_⟩
    apply (cancel_mono S.f).1
    rw [Category.assoc, hf, ← Category.assoc, hT.exact.lift_f]
    simp
  have : Epi g := by
    rw [epi_iff_surjective_up_to_refinements]
    intro W k
    obtain ⟨W', π, hπ, t, ht⟩ :=
      surjective_up_to_refinements_of_epi T.g (k ≫ R.f ≫ b.inv)
    have ht' : (t ≫ a.hom) ≫ S.g = 0 := by
      apply (cancel_mono c.hom).1
      rw [Category.assoc, Category.assoc, ← h, ← Category.assoc t T.g, ← ht]
      simp [Category.assoc]
    let l := hS.lift (t ≫ a.hom) ht'
    have hl : l ≫ S.f = t ≫ a.hom := hS.lift_f _ ht'
    refine ⟨W', π, hπ, l, ?_⟩
    apply (cancel_mono R.f).1
    rw [Category.assoc l g, hg, ← Category.assoc l S.f, hl]
    simpa [Category.assoc] using congrArg (fun z => z ≫ b.hom) ht
  exact ⟨g, hfg, ⟨ShortComplex.exact_of_f_is_kernel _ hker⟩, hg⟩

/-- **Nested kernels of compatible quotient sequences, in the original category.**  Given three
short exact sequences, isomorphisms identifying the middle terms of the first two and the
kernels with the terms of the third, and a morphism of the right-hand terms compatible with the
quotient maps, the kernels fit into a short exact sequence.

The induced morphism is reported together with the equation that *characterises* it,
`R.g ≫ φ = eb.hom ≫ T.f ≫ ea.inv ≫ S.g`. Since `R.g` is an epimorphism that equation pins `φ`
down uniquely, so a caller can name its own morphism, check the equation, and inherit short
exactness for it. Without the equation the morphism is anonymous and nothing downstream can
state a compatibility about it. -/
private theorem shortExact_kernels_of_quotients_with_comp
    {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜]
    (S T R : ShortComplex 𝒜) (hS : S.ShortExact) (hT : T.ShortExact) (hR : R.ShortExact)
    (ea : S.X₂ ≅ T.X₂) (eb : R.X₂ ≅ T.X₁) (ec : R.X₁ ≅ S.X₁)
    (ρ : S.X₃ ⟶ T.X₃) (hρ : S.g ≫ ρ = ea.hom ≫ T.g)
    (hdiag : R.f ≫ eb.hom ≫ T.f = ec.hom ≫ S.f ≫ ea.hom) :
    ∃ (φ : R.X₃ ⟶ S.X₃) (hz : φ ≫ ρ = 0), (ShortComplex.mk φ ρ hz).ShortExact ∧
      R.g ≫ φ = eb.hom ≫ T.f ≫ ea.inv ≫ S.g := by
  have mono_op_f : ∀ U : ShortComplex 𝒜, U.ShortExact → Mono U.op.f := fun U hU =>
    have := hU.epi_g
    inferInstanceAs (Mono U.g.op)
  have := mono_op_f S hS
  have := mono_op_f R hR
  have hdiag' : T.op.g ≫ eb.op.hom ≫ R.op.g = ea.op.hom ≫ S.op.g ≫ ec.op.hom :=
    Quiver.Hom.unop_inj (by
      change (R.f ≫ eb.hom) ≫ T.f = (ec.hom ≫ S.f) ≫ ea.hom
      rw [Category.assoc, Category.assoc]
      exact hdiag)
  have hρ' : ρ.op ≫ S.op.f = T.op.f ≫ ea.op.hom :=
    Quiver.Hom.unop_inj (by
      change S.g ≫ ρ = ea.hom ≫ T.g
      exact hρ)
  obtain ⟨g, hz, hse, hchar⟩ := shortExact_kernels_of_shortExact_quotients_with_comp
    S.op T.op R.op hS.exact.op hT.op hR.exact.op ea.op eb.op ec.op hdiag' ρ.op hρ'
  refine ⟨g.unop, (ShortComplex.mk ρ.op g hz).unop.zero, hse.unop, ?_⟩
  have h := congrArg Quiver.Hom.unop hchar
  simp only [unop_comp, Category.assoc] at h
  exact h

section SumSequence

open Stacks.SheafOfModules.TensorStalkRingedSpace

variable {X : Scheme.{u}}

/-- **Tag 0C4T with the sum written out.**  For `C` and `D` closed subschemes of `X` with `D` an
effective Cartier divisor, the structure sheaf of the sum `C + D` is an extension of the
structure sheaf of `D` by `𝒪_X(-D)|_C`.

The kernel inclusion is reported together with the equation that *characterises* it: composing
it with the surjection `ℐ_D ⟶ 𝒪_X(-D)|_C` gives `ℐ_D ⟶ 𝒪_X ⟶ 𝒪_{C + D}`. That surjection is an
epimorphism, so the equation pins the inclusion down uniquely. -/
private lemma addEffectiveCartierDivisor_shortExact_aux_with_comp (D C : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hsub : C * D ≤ D)
    (hleft : (toSchemeComplex (idealQuotientComplex (C * D))).g ≫ quotientRestriction hsub =
      (Iso.refl (toSchemeComplex (idealQuotientComplex (C * D))).X₂).hom ≫
        (toSchemeComplex (idealQuotientComplex D)).g)
    (hright : (toSchemeComplex (idealTensorComplex C D hD)).f ≫
          (Iso.refl (toSchemeComplex (idealTensorComplex C D hD)).X₂).hom ≫
            (toSchemeComplex (idealQuotientComplex D)).f =
        (idealTensorMulIso C D hD).hom ≫ (toSchemeComplex (idealQuotientComplex (C * D))).f ≫
          (Iso.refl (toSchemeComplex (idealQuotientComplex (C * D))).X₂).hom) :
    ∃ f : (toSchemeComplex (idealTensorComplex C D hD)).X₃ ⟶
        (toSchemeComplex (idealQuotientComplex (C * D))).X₃,
      ∃ zero : f ≫ quotientRestriction hsub = 0,
        (ShortComplex.mk f (quotientRestriction hsub) zero).ShortExact ∧
          (toSchemeComplex (idealTensorComplex C D hD)).g ≫ f =
            Stacks.IdealSheafSequence.divisorIdealMap D ≫
              Stacks.IdealSheafSequence.divisorQuotientMap (C * D) :=
  by
  obtain ⟨φ, hz, hse, hchar⟩ := shortExact_kernels_of_quotients_with_comp (𝒜 := X.Modules)
    (toSchemeComplex (idealQuotientComplex (C * D)))
    (toSchemeComplex (idealQuotientComplex D))
    (toSchemeComplex (idealTensorComplex C D hD))
    (shortExact_toSchemeComplex (shortExact_idealQuotientComplex (C * D)))
    (shortExact_toSchemeComplex (shortExact_idealQuotientComplex D))
    (shortExact_toSchemeComplex (shortExact_idealTensorComplex C D hD))
    (Iso.refl _) (Iso.refl _) (idealTensorMulIso C D hD) (quotientRestriction hsub) hleft hright
  refine ⟨φ, hz, hse, hchar.trans ?_⟩
  rw [Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.id_comp]
  rfl

/-! ### Tag 0C4T with the kernel inclusion named

`Stacks.Divisors.addEffectiveCartierDivisor_shortExact` asserts that the sequence *exists*: its
kernel inclusion `𝒪_X(-D)|_C ⟶ 𝒪_{D'}` is bound by an existential quantifier, so a consumer can
use the sequence but cannot state an equation about its first map. The left exactness of global
sections then identifies `Γ(X, 𝒪_X(-D)|_C)` with the kernel of `Γ(X, 𝒪_{D'}) ⟶ Γ(X, 𝒪_D)` only
up to that unnamed choice, which is not enough to say anything multiplicative about the
identification — and multiplicativity across degrees is exactly what the graded pieces of a
formal neighbourhood need (see
`StacksFrontier/AlgebraicGeometry/Surfaces/ExceptionalCurveFormalNeighborhood.lean`).

The map is canonical, though, and this section names it. `ℐ_C ⊗ ℐ_D ⟶ ℐ_D` has cokernel
`i_*i^*ℐ_D = 𝒪_X(-D)|_C`, and the composite `ℐ_C ⊗ ℐ_D ⟶ ℐ_D ⟶ 𝒪_X ⟶ 𝒪_{C + D}` vanishes
because `ℐ_C · ℐ_D` is the ideal sheaf of `C + D`
(`Stacks.Divisors.idealTensorToUnit_comp_divisorQuotientMap`). So `ℐ_D ⟶ 𝒪_X ⟶ 𝒪_{C + D}`
descends along the cokernel, and that descent is the kernel inclusion of the sequence. -/

/-- Multiplying two ideal sheaves into `𝒪_X` and projecting to `𝒪_{C + D}` is zero: the product
`ℐ_C · ℐ_D` is the ideal sheaf of `C + D`, which is the kernel of the projection.

The zero morphism is written as the preimage of `0` under
`SheafOfModules.fullyFaithfulForget`, the spelling this file uses throughout
(`Stacks.Divisors.idealTensorToUnit_comp_divisorQuotientMap`,
`Stacks.Divisors.idealTensor_comp_unit_eq_zero`).  The source of the composite is read in
`SheafOfModules` over `Stacks.SheafOfModules.Tensor.ringSheaf` and its target in
`SheafOfModules` over `structureSheafRing`; the two readings are definitionally equal but not
syntactically so, and a bare `0` leaves the ambient category of the equation spelled across
both, where instance search cannot find its zero morphisms.  Naming the ring sheaf in the
preimage pins the reading. -/
private lemma idealTensorComplex_f_comp_divisorIdealMap_comp_divisorQuotientMap
    (C D : X.IdealSheafData) (hD : IsEffectiveCartierDivisor D) :
    (idealTensorComplex C D hD).f ≫ Stacks.IdealSheafSequence.divisorIdealMap D ≫
        Stacks.IdealSheafSequence.divisorQuotientMap (C * D) =
      (SheafOfModules.fullyFaithfulForget
        (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)).preimage 0 :=
  (Category.assoc _ _ _).symm.trans (idealTensorToUnit_comp_divisorQuotientMap C D)

/-- **The kernel inclusion of the sequence of [Stacks, Tag 0C4T], as a named morphism.** The
restriction `𝒪_X(-D)|_C` of the ideal sheaf of `D` to `C` maps to the structure sheaf of the sum
`C + D`, by descending `ℐ_D ⟶ 𝒪_X ⟶ 𝒪_{C + D}` along the cokernel `ℐ_D ⟶ i_*i^*ℐ_D`.

This is the morphism that `Stacks.Divisors.addEffectiveCartierDivisor_shortExact` produces
existentially; `Stacks.Divisors.eq_sumKernelMap` records that it is the only morphism with its
characteristic property, and `Stacks.Divisors.shortExact_sumKernelMap` is the tag's short exact
sequence stated about *this* morphism. -/
@[no_expose, sga "7 X 1.13"]
public noncomputable def sumKernelMap (D C : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) :
    (Scheme.Modules.pushforward C.subschemeι).obj
        ((Scheme.Modules.pullback C.subschemeι).obj (negativeTwist D)) ⟶
      Scheme.IdealSheafData.closedSubschemeStructureSheaf (C * D) :=
  haveI := (shortExact_idealTensorComplex C D hD).epi_g
  (shortExact_idealTensorComplex C D hD).exact.desc
    (Stacks.IdealSheafSequence.divisorIdealMap D ≫
      Stacks.IdealSheafSequence.divisorQuotientMap (C * D))
    (idealTensorComplex_f_comp_divisorIdealMap_comp_divisorQuotientMap C D hD)

/-- **The characteristic property of the named kernel inclusion.** Precomposing with the
surjection `ℐ_D ⟶ 𝒪_X(-D)|_C` — the unit of `i^* ⊣ i_*` at `ℐ_D` — gives the inclusion of `ℐ_D`
into `𝒪_X` followed by the projection to `𝒪_{C + D}`. Since that surjection is an epimorphism
the equation determines the morphism. -/
public lemma unit_comp_sumKernelMap (D C : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) :
    (modulePullbackPushforwardAdjunction C.subschemeι.toLRSHom.toShHom).unit.app
          (negativeTwist D) ≫ sumKernelMap D C hD =
      Stacks.IdealSheafSequence.divisorIdealMap D ≫
        Stacks.IdealSheafSequence.divisorQuotientMap (C * D) :=
  have := (shortExact_idealTensorComplex C D hD).epi_g
  (shortExact_idealTensorComplex C D hD).exact.g_desc _
    (idealTensorComplex_f_comp_divisorIdealMap_comp_divisorQuotientMap C D hD)

/-- **The named kernel inclusion is the only morphism with its characteristic property.**

The cancellation is spelled at `Stacks.Divisors.idealTensorComplex`'s own `g` rather than at the
unit of the adjunction, which is the same morphism: `CategoryTheory.Epi` carries the ambient
category as an argument, so the epimorphism supplied by
`CategoryTheory.ShortComplex.ShortExact.epi_g` — which lives over
`Stacks.SheafOfModules.Tensor.ringSheaf` — is not the instance that a goal over
`structureSheafRing` asks for, even though the two categories are definitionally equal. -/
public lemma eq_sumKernelMap (D C : X.IdealSheafData) (hD : IsEffectiveCartierDivisor D)
    (f : (Scheme.Modules.pushforward C.subschemeι).obj
        ((Scheme.Modules.pullback C.subschemeι).obj (negativeTwist D)) ⟶
      Scheme.IdealSheafData.closedSubschemeStructureSheaf (C * D))
    (hf : (modulePullbackPushforwardAdjunction C.subschemeι.toLRSHom.toShHom).unit.app
          (negativeTwist D) ≫ f =
        Stacks.IdealSheafSequence.divisorIdealMap D ≫
          Stacks.IdealSheafSequence.divisorQuotientMap (C * D)) :
    f = sumKernelMap D C hD :=
  have := (shortExact_idealTensorComplex C D hD).epi_g
  (cancel_epi (idealTensorComplex C D hD).g).1
    (hf.trans (unit_comp_sumKernelMap D C hD).symm)

/-- The sequence of Tag 0C4T with the sum written out, stated about the named kernel inclusion. -/
private lemma exists_shortExact_sumKernelMap (D C : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hsub : C * D ≤ D) :
    ∃ zero : sumKernelMap D C hD ≫ Scheme.IdealSheafData.closedSubschemeRestriction hsub = 0,
      (ShortComplex.mk (sumKernelMap D C hD)
        (Scheme.IdealSheafData.closedSubschemeRestriction hsub) zero).ShortExact := by
  obtain ⟨f, zero, hse, hchar⟩ := addEffectiveCartierDivisor_shortExact_aux_with_comp D C hD hsub
    (quotientRestriction_diagram hsub) (idealTensorComplex_diagram C D hD)
  obtain rfl : f = sumKernelMap D C hD := eq_sumKernelMap D C hD f hchar
  exact ⟨zero, hse⟩

/-- The named kernel inclusion composed with the restriction `𝒪_{C + D} ⟶ 𝒪_D` is zero. -/
public lemma sumKernelMap_comp_closedSubschemeRestriction (D C : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hsub : C * D ≤ D) :
    sumKernelMap D C hD ≫ Scheme.IdealSheafData.closedSubschemeRestriction hsub = 0 :=
  (exists_shortExact_sumKernelMap D C hD hsub).1

/-- **[Stacks, Tag 0C4T] with its kernel inclusion named.** For `D ⊆ D'` effective Cartier
divisors on a scheme `X` and `C` an effective Cartier divisor with `D' = D + C`, the sequence
`0 ⟶ 𝒪_X(-D)|_C ⟶ 𝒪_{D'} ⟶ 𝒪_D ⟶ 0` is short exact, with first map
`Stacks.Divisors.sumKernelMap` and second map the canonical restriction.

`Stacks.Divisors.addEffectiveCartierDivisor_shortExact` is the same assertion with the first map
bound by an existential; this version is the one a consumer needs in order to state an equation
about that map, and `Stacks.Divisors.eq_sumKernelMap` shows the two are about the same morphism.
The sum is written `C * D` rather than `D * C` because the named morphism's type mentions it, so
no `mul_comm` can be absorbed into a proof. -/
@[stacks 0C4T "with the kernel inclusion named, rather than existentially bound",
  sga "7 X 1.13" "more general"]
public theorem shortExact_sumKernelMap (D C : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hsub : C * D ≤ D) :
    (ShortComplex.mk (sumKernelMap D C hD)
      (Scheme.IdealSheafData.closedSubschemeRestriction hsub)
      (sumKernelMap_comp_closedSubschemeRestriction D C hD hsub)).ShortExact :=
  (exists_shortExact_sumKernelMap D C hD hsub).2

end SumSequence

end Stacks.Divisors

end
