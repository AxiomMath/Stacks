module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PuncturedSpectrumSectionsDepthTwo
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.LiftFromHypersurface

/-!
# Lifting a finite étale cover from the hypersurface section in depth at least three

Work in the local Lefschetz situation of Tag 0BLF: `A` is a Noetherian local ring with maximal
ideal `𝔪`, `f ∈ 𝔪`, `X = Spec A`, `X₀ = Spec (A / fA)`, and `U`, `U₀` are the punctured spectra
of `A` and of `A / fA`. Let `V` be finite étale over `U` and suppose that `V₀ = V ×_U U₀` already
comes from `X₀`, that is `V₀ = Y₀ ×_{X₀} U₀` for some `Y₀ → X₀` finite étale. If `A` has depth at
least `3` then `V` itself comes from `X`: `V = Y ×_X U` for some `Y → X` finite étale.

This is the source's two-line proof. Depth at least `3` forces `H¹_𝔪(A) = H²_𝔪(A) = 0` by
Tag 0AVZ, so the annihilation hypothesis of Tag 0BLS holds with exponent `0`, and that lemma
produces the cover `Y → X`.

## Main results

* `AlgebraicGeometry.LocalLefschetzSituation.exists_finiteEtale_extension_of_three_le_depth`
  — **Stacks 0BLM**, in the generality of Tag 0BLF, with Tag 0BLS carried as a hypothesis.
* `…LocalLefschetzSituation.exists_finiteEtale_extension_of_three_le_depth_of_isAdicComplete`
  — the same conclusion for an `f`-adically complete `A`, with Tag 0BLS discharged from
  `exists_finiteEtale_extension_of_annihilated`.

## What is and is not proved

The mathematical content of Tag 0BLM is the passage from the depth hypothesis to the vanishing
of `H¹_𝔪(A)` and `H²_𝔪(A)`, after which the source quotes Tag 0BLS. That passage is proved
outright here, from `Stacks.LocalCohomology.subsingleton_localCohomologyModule_of_lt_depth`.

Tag 0BLS enters twice, in two different ways, and the two results above differ only in that.

* `exists_finiteEtale_extension_of_three_le_depth` has exactly the hypotheses of the tag — `A` a
  Noetherian local ring with `f ∈ 𝔪`, depth at least `3`, and `V₀` coming from `X₀` — and takes
  Tag 0BLS as the named hypothesis `hLiftFromHypersurface`, stated in the unrestricted form the
  source gives it and universally quantified over all local Lefschetz situations. It is not
  specialised to the situation at hand, mentions no depth, and does not grant the conclusion:
  its own hypothesis is the annihilation of `H¹_𝔪` and `H²_𝔪` by a power of `f`.
* `exists_finiteEtale_extension_of_three_le_depth_of_isAdicComplete` discharges that hypothesis
  from `exists_finiteEtale_extension_of_annihilated`, the special case of Tag 0BLS for an
  `f`-adically complete `A`, and so inherits that lemma's restrictions: `A` is assumed
  `f`-adically complete, the source's reduction to that case through Tag 0BLL and Tag 0ALZ not
  being carried out there, and `hEKP`, `h0GN2` and `halgebra` are granted. Those three are
  statements about arbitrary Noetherian rings and arbitrary schemes and closed immersions —
  `hEKP` is the chain (1) ⇒ (4) of Tag 0EKP, `h0GN2` is Tag 0GN2 in the shape Tag 0EL8 uses, and
  `halgebra` is the multiplicativity criterion of Tag 0EL8 — and none of them mentions `A`, `f`,
  `U` or `U₀`.

No henselian hypothesis is assumed anywhere, matching the tag.

## Implementation notes

The situation is `AlgebraicGeometry.LocalLefschetzSituation` of
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.LocalLefschetz`, the structure
carrying Tag 0BLF over which the rest of the `PurityLocalCase` material is stated; the
development has a second structure of the same name,
`Stacks.FundamentalGroup.LocalLefschetzSituation`, which is not the one used here.

Depth is `Module.depth A 𝔪 A` and local cohomology is
`Stacks.LocalCohomology.localCohomologyModule`, the coreflection model in which Tag 0BLS asks
for its hypothesis; the development also has `Dualizing.localCohomology` and
`Stacks.LocalCohomology.localCohomologyWithSupportIn`, which are different constants.
"`V = Y ×_X U`" is recorded as a `CategoryTheory.IsPullback` square rather than an equality of
schemes, and likewise the hypothesis on `V₀`; `V ×_U U₀` is the chosen pullback
`pullback pi S.U₀ToU`.

## References

* [Stacks Project, Tag 0AVZ](https://stacks.math.columbia.edu/tag/0AVZ)
* [Stacks Project, Tag 0BLF](https://stacks.math.columbia.edu/tag/0BLF)
* [Stacks Project, Tag 0BLM](https://stacks.math.columbia.edu/tag/0BLM)
* [Stacks Project, Tag 0BLS](https://stacks.math.columbia.edu/tag/0BLS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing
open Stacks.FundamentalGroup Stacks.RelativeSpec
open Stacks.LocalCohomology (complementZeroLocus localCohomologyModule)
open Stacks.Algebraization (CompletionFullyFaithfulOnFiniteLocallyFree
  complementPrincipalIdealSheaf)

attribute [local instance 2000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- Below the depth of a Noetherian local ring `A` the local cohomology `H^i_𝔪(A)` is zero, so
every power of every element of `A` annihilates it.  This is the shape in which [Stacks, Tag
0BLS] asks for its hypothesis on `H¹_𝔪(A)` and `H²_𝔪(A)`. -/
private theorem exists_pow_smul_localCohomologyModule_eq_zero_of_lt_depth (A : Type u)
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (i : ℕ)
    (hi : i < 3) (hdepth : 3 ≤ Module.depth A (maximalIdeal A) A) (g : A) :
    ∃ n : ℕ, ∀ x : localCohomologyModule A (maximalIdeal A)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal A)) (ModuleCat.of A A) i,
      g ^ n • x = 0 :=
  ⟨0, fun _ =>
    (Stacks.LocalCohomology.subsingleton_localCohomologyModule_of_lt_depth A (maximalIdeal A)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal A)) (ModuleCat.of A A)
      (by simpa using (maximalIdeal.isMaximal A).ne_top) i
      (lt_of_lt_of_le (by exact_mod_cast hi) hdepth)).elim _ _⟩

namespace LocalLefschetzSituation

/-- Depth at least `3` lets a finite étale cover of `U` whose restriction to `U₀` comes from
`X₀` be extended over `X`, for an `f`-adically complete `A`.  This is a special case of
[Stacks, Tag 0BLM]; see also `exists_finiteEtale_extension_of_three_le_depth` below.

Depth at least `3` makes `H¹_𝔪(A)` and `H²_𝔪(A)` vanish, by [Stacks, Tag 0AVZ], so they are
annihilated by `f ^ 0` and `exists_finiteEtale_extension_of_annihilated` applies.  The
completeness hypothesis and the three general hypotheses `hEKP`, `h0GN2` and `halgebra` are
passed to that lemma unchanged; the depth hypothesis is consumed here, not carried. -/
public theorem exists_finiteEtale_extension_of_three_le_depth_of_isAdicComplete
    (S : LocalLefschetzSituation.{u})
    (hdepth : 3 ≤ Module.depth S.A (maximalIdeal S.A) S.A)
    (hcomplete : IsAdicComplete (Ideal.span {S.f}) S.A)
    (hEKP : ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] (b : Ideal B) (g : B),
      Scheme.IsQuasiAffine (complementZeroLocus B b : Scheme) →
      Function.Bijective
        (Stacks.Algebraization.ComplementTower.sectionsToLimit B b g (ModuleCat.of B B)) →
      CompletionFullyFaithfulOnFiniteLocallyFree (complementZeroLocus B b : Scheme)
        (complementPrincipalIdealSheaf B b g))
    (h0GN2 : ∀ {Z Z' : Scheme.{u}} (κ : Z' ⟶ Z) [IsClosedImmersion κ] (N : Z.Modules),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N →
      Stacks.Algebraization.IsInfinitesimalSectionsComplete κ
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N) →
      (∀ φ ψ : N ⟶ SheafOfModules.unit Z.ringCatSheaf,
          (∀ n : ℕ, φ ≫ nthOrderUnitMap κ n = ψ ≫ nthOrderUnitMap κ n) → φ = ψ) ∧
        ∀ α : ∀ n : ℕ, N ⟶ AlgebraSheaf.underlyingModule (nthOrderAlgebra κ n),
          (∀ n : ℕ, α (n + 1) ≫ nthOrderTransitionMap κ n = α n) →
          ∃ φ : N ⟶ SheafOfModules.unit Z.ringCatSheaf,
            ∀ n : ℕ, φ ≫ nthOrderUnitMap κ n = α n)
    (halgebra : ∀ {Z : Scheme.{u}} (B C : AlgebraSheaf Z) (D : ℕ → AlgebraSheaf Z)
      (r : ∀ n : ℕ, C ⟶ D n)
      (φ : AlgebraSheaf.underlyingModule B ⟶ AlgebraSheaf.underlyingModule C),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (AlgebraSheaf.underlyingModule B) →
      _root_.SheafOfModules.IsCoherent (AlgebraSheaf.underlyingModule B) →
      (∀ n : ℕ, ∃ ψ : B ⟶ D n,
        AlgebraSheaf.underlyingModuleMap ψ = φ ≫ AlgebraSheaf.underlyingModuleMap (r n)) →
      (∀ P : Z.Modules, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} P →
        _root_.SheafOfModules.IsCoherent P →
        ∀ a b : P ⟶ AlgebraSheaf.underlyingModule C,
          (∀ n : ℕ, a ≫ AlgebraSheaf.underlyingModuleMap (r n) =
            b ≫ AlgebraSheaf.underlyingModuleMap (r n)) → a = b) →
      ∃ ψ : B ⟶ C, AlgebraSheaf.underlyingModuleMap ψ = φ)
    (V : Scheme.{u}) (pi : V ⟶ S.U) [IsFinite pi] [Etale pi]
    (Y₀ : Scheme.{u}) (f₀ : Y₀ ⟶ S.X₀) [IsFinite f₀] [Etale f₀]
    (g₀ : pullback pi S.U₀ToU ⟶ Y₀)
    (h₀ : IsPullback (pullback.snd pi S.U₀ToU) g₀ S.U₀Open.ι f₀) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ S.X) (g : V ⟶ Y),
      IsFinite p ∧ Etale p ∧ IsPullback pi g S.UOpen.ι p :=
  exists_finiteEtale_extension_of_annihilated S hcomplete
    (exists_pow_smul_localCohomologyModule_eq_zero_of_lt_depth S.A 1 (by norm_num) hdepth S.f)
    (exists_pow_smul_localCohomologyModule_eq_zero_of_lt_depth S.A 2 (by norm_num) hdepth S.f)
    hEKP h0GN2 halgebra V pi Y₀ f₀ g₀ h₀

/-- **[Stacks, Tag 0BLM]** In the local Lefschetz situation let `V` be finite étale over `U` and
assume (1) `A` has depth at least `3`, and (2) `V ×_U U₀` is `Y₀ ×_{X₀} U₀` for some
`Y₀ → X₀` finite étale.  Then `V = Y ×_X U` for some `Y → X` finite étale.

This is the source's proof.  Depth at least `3` forces `H¹_𝔪(A) = H²_𝔪(A) = 0` by
[Stacks, Tag 0AVZ], which is the whole content supplied here, and the conclusion is then
[Stacks, Tag 0BLS] at the situation `S`.

That last step is the hypothesis `hLiftFromHypersurface`, stated in the unrestricted form the
source gives [Stacks, Tag 0BLS], universally quantified over all local Lefschetz situations, with
its own annihilation hypothesis intact — it is not specialised to `S`, says nothing about depth,
and does not grant this statement's conclusion.  It holds by
`exists_finiteEtale_extension_of_localCohomology_annihilated`.  The `f`-adically complete case is
`exists_finiteEtale_extension_of_three_le_depth_of_isAdicComplete` above, where it is
discharged. -/
@[stacks 0BLM "the unrestricted Stacks 0BLS is carried as a named general hypothesis"]
public theorem exists_finiteEtale_extension_of_three_le_depth
    (S : LocalLefschetzSituation.{u})
    (hdepth : 3 ≤ Module.depth S.A (maximalIdeal S.A) S.A)
    (hLiftFromHypersurface : ∀ T : LocalLefschetzSituation.{u},
      (∃ n : ℕ, ∀ x : localCohomologyModule T.A (maximalIdeal T.A)
        (Ideal.fg_of_isNoetherianRing (maximalIdeal T.A)) (ModuleCat.of T.A T.A) 1,
        T.f ^ n • x = 0) →
      (∃ n : ℕ, ∀ x : localCohomologyModule T.A (maximalIdeal T.A)
        (Ideal.fg_of_isNoetherianRing (maximalIdeal T.A)) (ModuleCat.of T.A T.A) 2,
        T.f ^ n • x = 0) →
      ∀ (W : Scheme.{u}) (ρ : W ⟶ T.U), IsFinite ρ → Etale ρ →
      ∀ (Z₀ : Scheme.{u}) (q₀ : Z₀ ⟶ T.X₀), IsFinite q₀ → Etale q₀ →
      ∀ e₀ : pullback ρ T.U₀ToU ⟶ Z₀,
        IsPullback (pullback.snd ρ T.U₀ToU) e₀ T.U₀Open.ι q₀ →
        ∃ (Z : Scheme.{u}) (q : Z ⟶ T.X) (e : W ⟶ Z),
          IsFinite q ∧ Etale q ∧ IsPullback ρ e T.UOpen.ι q)
    (V : Scheme.{u}) (pi : V ⟶ S.U) [IsFinite pi] [Etale pi]
    (Y₀ : Scheme.{u}) (f₀ : Y₀ ⟶ S.X₀) [IsFinite f₀] [Etale f₀]
    (g₀ : pullback pi S.U₀ToU ⟶ Y₀)
    (h₀ : IsPullback (pullback.snd pi S.U₀ToU) g₀ S.U₀Open.ι f₀) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ S.X) (g : V ⟶ Y),
      IsFinite p ∧ Etale p ∧ IsPullback pi g S.UOpen.ι p :=
  hLiftFromHypersurface S
    (exists_pow_smul_localCohomologyModule_eq_zero_of_lt_depth S.A 1 (by norm_num) hdepth S.f)
    (exists_pow_smul_localCohomologyModule_eq_zero_of_lt_depth S.A 2 (by norm_num) hdepth S.f)
    V pi inferInstance inferInstance Y₀ f₀ inferInstance inferInstance g₀ h₀

end LocalLefschetzSituation

end AlgebraicGeometry

end
