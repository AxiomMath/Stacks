module

public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.FullyFaithfulComplete
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TopologicalInvarianceFundamental.Basic
public import StacksFrontier.RingTheory.Henselian.Pair.Criteria

/-!
# Lifting a finite étale cover from the hypersurface section

Work in the local Lefschetz situation of Tag 0BLF: `A` is a Noetherian local ring with maximal
ideal `𝔪`, `f ∈ 𝔪`, `X = Spec A`, `X₀ = Spec (A / fA)`, and `U`, `U₀` are the punctured spectra
of `A` and of `A / fA`. Let `V` be finite étale over `U` and suppose `V₀ = V ×_U U₀` already
comes from `X₀`, i.e. `V₀ = Y₀ ×_{X₀} U₀` for some `Y₀ → X₀` finite étale. The two lemmas here
give conditions under which `V` itself comes from `X`: `V = Y ×_X U` for some `Y → X` finite
étale.

Both are the two-step argument of the source. Base change along the closed immersion `X₀ ⟶ X`
is an *equivalence* on finite étale covers when `(A, fA)` is a henselian pair — Stacks 09ZS, the
scheme form of the lifting lemma Stacks 09ZL that the source quotes — so `Y₀` lifts to a finite
étale `Y → X`. Restriction `FÉt_U ⟶ FÉt_{U₀}` is *fully faithful* under the hypotheses of the
lemma, by Stacks 0BM6 for Tag 0BLS and by Stacks 0EK5 for Tag 0EK6, so the isomorphism
`V ×_U U₀ ≅ (Y ×_X U) ×_U U₀` descends to `V ≅ Y ×_X U`.

## Main results

* `AlgebraicGeometry.LocalLefschetzSituation.exists_finiteEtale_extension_of_depth`
  — the special case of Stacks 0EK6 under hypothesis (c)(ii) and for an `f`-adically complete
  `A`; the tag itself is
  `…LocalLefschetzSituation.exists_finiteEtale_extension_of_dualizingComplex`.
* `AlgebraicGeometry.LocalLefschetzSituation.exists_finiteEtale_extension_of_annihilated`
  — the special case of Stacks 0BLS for an `f`-adically complete `A`; the tag itself, with no
  such restriction, is
  `…LocalLefschetzSituation.exists_finiteEtale_extension_of_localCohomology_annihilated`.

## What is and is not proved

The descent step is proved outright. The full faithfulness of restriction is taken from this
development's carriers of the two source lemmas it needs,
`…fullyFaithful_finiteEtaleRestriction_of_annihilated` (Stacks 0BM6) and
`…fullyFaithful_finiteEtaleRestriction_of_depth` (Stacks 0EK5), and the restrictions under which
*those* are available are inherited verbatim. Nothing further is assumed. Concretely the
inherited restrictions are:

* `A` is assumed `f`-adically complete (`hcomplete`). The source's proofs of both tags reduce to
  that case by replacing `A` by its `𝔪`-adic completion `Â` — Stacks 0BLL, available here as
  `AlgebraicGeometry.exists_finiteEtale_extension_iff_completion`, together with Stacks 0ALJ for
  the henselianness of the complete pair — and the reduction is not carried out, neither here
  nor in the two full-faithfulness carriers.
* For Tag 0EK6 only branch (ii) of the source's hypothesis (c) is treated, exactly as in the
  Stacks 0EK5 carrier; branch (c)(i) is not reduced to (ii).
* `hEKP`, `h0GN2` and `halgebra` are the three general hypotheses carried by the two
  full-faithfulness carriers. Each is a statement about arbitrary Noetherian rings or arbitrary
  schemes and closed immersions — `hEKP` is the chain (1) ⇒ (4) of Stacks 0EKP, `h0GN2` is
  Stacks 0GN2 in the shape Stacks 0EL8 uses, and `halgebra` is the multiplicativity criterion of
  Stacks 0EL8. None mentions `A`, `f`, `U` or `U₀`.

For Tag 0BLS the henselian-pair hypothesis is *not* carried: `(A, fA)` henselian is derived from
`hcomplete` (Stacks 0ALJ), so the only hypotheses of that theorem beyond the tag's own are
`hcomplete` and the three general ones. For Tag 0EK6 the henselian-pair hypothesis `hS` is the
tag's own hypothesis (b), and here it is genuinely used — it is what feeds Stacks 09ZS.

## Implementation notes

The situation is `AlgebraicGeometry.LocalLefschetzSituation`, the structure of
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.LocalLefschetz` carrying Tag
0BLF. The development contains a second structure of the same name,
`Stacks.FundamentalGroup.LocalLefschetzSituation` in
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalLefschetzSituation`; the one used here is
the `AlgebraicGeometry` one, over which the rest of the `PurityLocalCase` material — and in
particular the two full-faithfulness carriers consumed below — is stated.

`FÉt_X` is `AlgebraicGeometry.FiniteEtaleOver X` and restriction is
`AlgebraicGeometry.finiteEtaleBaseChange`. "`V = Y ×_X U`" is recorded as a
`CategoryTheory.IsPullback` square rather than an equality of schemes, and likewise the
hypothesis on `V₀`; `V ×_U U₀` is the chosen pullback `pullback pi S.U₀ToU`.

Local cohomology `Hⁱ_𝔪(A)` is `Stacks.LocalCohomology.localCohomologyModule`, the same spelling
the Stacks 0BM6 carrier uses, so that the hypothesis passes through unchanged; note that the
development also has `Dualizing.localCohomology` and
`Stacks.LocalCohomology.localCohomologyWithSupportIn`, which are different constants.

`henselianPair_of_isAdicComplete` duplicates, for an `I`-adically complete ring, a lemma that
exists in the development only as a `private` declaration inside
`StacksFrontier/Homology/DerivedComplete/PrincipalHenselianPair.lean`; it is `private` here too.

## References

* [Stacks Project, Tag 0BLF](https://stacks.math.columbia.edu/tag/0BLF)
* [Stacks Project, Tag 0BLS](https://stacks.math.columbia.edu/tag/0BLS)
* [Stacks Project, Tag 0EK6](https://stacks.math.columbia.edu/tag/0EK6)
* [Stacks Project, Tag 09ZS](https://stacks.math.columbia.edu/tag/09ZS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing
open Stacks.FundamentalGroup Stacks.RelativeSpec
open Stacks.LocalCohomology (complementZeroLocus localCohomologyModule)
open Stacks.Algebraization (CompletionFullyFaithfulOnFiniteLocallyFree
  complementPrincipalIdealSheaf enatToEInt krullDimToEInt)

attribute [local instance 2000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

namespace LocalLefschetzSituation

/-- An `I`-adically complete ring forms a henselian pair with `I`.

`IsAdicComplete.henselianRing` gives Mathlib's Newton-lifting form of henselianness; the
monic-factorization form of `HenselianPair` follows through Gabber's unique-root criterion, item
(5) of `henselianPair_tfae`. This is Stacks 0ALJ; the development proves it only as a `private`
lemma inside `StacksFrontier/Homology/DerivedComplete/PrincipalHenselianPair.lean`, so the argument
is repeated here. -/
@[sga "3 X 4.0" "Recall 4.0"]
private lemma henselianPair_of_isAdicComplete (A : Type u) [CommRing A] (I : Ideal A)
    [IsAdicComplete I A] : HenselianPair A I := by
  let : HenselianRing A I := IsAdicComplete.henselianRing A I
  apply ((henselianPair_tfae.{u, u} A I).out 5 1).mp
  refine ⟨HenselianRing.jac, ?_⟩
  intro f hf n hn a hfa
  have hf1 : f.eval 1 ∈ I := by
    rw [hfa]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_finsetSum, Polynomial.eval_C, one_pow, sub_self, mul_zero,
      zero_add, mul_one]
    exact I.sum_mem fun i _ ↦ (a i).property
  have hder : IsUnit (Ideal.Quotient.mk I (f.derivative.eval 1)) := by
    have hsum : Polynomial.eval 1
        (Polynomial.derivative (∑ i : Fin (n + 1),
          Polynomial.C (a i : A) * Polynomial.X ^ (i : ℕ))) ∈ I := by
      rw [map_sum, Polynomial.eval_finsetSum]
      apply Submodule.sum_mem
      intro i _
      simp only [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul,
        Polynomial.derivative_pow, zero_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, one_pow, mul_one]
      exact I.mul_mem_right _ (a i).property
    have heq : Ideal.Quotient.mk I (f.derivative.eval 1) = 1 := by
      rw [hfa]
      simp only [Polynomial.derivative_mul, Polynomial.derivative_pow,
        Polynomial.derivative_X, Polynomial.derivative_sub, Polynomial.derivative_one,
        zero_add, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one,
        one_pow, sub_self, mul_zero, one_mul, map_add]
      rw [show Ideal.Quotient.mk I
          (Polynomial.eval 1 (Polynomial.derivative
            (∑ i : Fin (n + 1), Polynomial.C (a i : A) * Polynomial.X ^ (i : ℕ)))) = 0 by
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hsum]
      simp
    rw [heq]
    exact isUnit_one
  obtain ⟨α, hroot, hα⟩ := HenselianRing.is_henselian f hf 1 hf1 hder
  refine ⟨α, ⟨hα, hroot⟩, ?_⟩
  intro β hβ
  obtain ⟨k, hk⟩ := f.binomExpansion α (β - α)
  rw [add_sub_cancel] at hk
  rw [Polynomial.IsRoot] at hroot hβ
  rw [hroot, hβ.2, zero_add] at hk
  set y := β - α with hy
  have hymem : y ∈ I := by
    rw [hy, show β - α = (β - 1) - (α - 1) by ring]
    exact I.sub_mem hβ.1 hα
  have hfactor : y * (f.derivative.eval α + k * y) = 0 := by
    linear_combination -hk
  have hunit : IsUnit (f.derivative.eval α + k * y) := by
    let : IsLocalHom (Ideal.Quotient.mk I) :=
      isLocalHom_of_le_jacobson_bot I HenselianRing.jac
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    have hαeq : Ideal.Quotient.mk I α = Ideal.Quotient.mk I 1 := by
      rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact hα
    have hyq : Ideal.Quotient.mk I y = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hymem
    rw [map_add, map_mul, hyq, mul_zero, add_zero, ← Polynomial.eval_map_apply, hαeq,
      Polynomial.eval_map_apply]
    exact hder
  have hy0 : y = 0 := (IsUnit.mul_left_eq_zero hunit).mp hfactor
  rw [hy] at hy0
  exact sub_eq_zero.mp hy0

/-- The descent step shared by Tags 0BLS and 0EK6. Granted that base change along the closed
immersion `X₀ ⟶ X` is an equivalence on finite étale covers and that restriction along
`U₀ ⟶ U` is fully faithful, a finite étale `V ⟶ U` whose restriction to `U₀` comes from `X₀`
itself comes from `X`.

The equivalence produces a finite étale `Y ⟶ X` with `Y ×_X X₀ ≅ Y₀`. Since
`U₀ ⟶ U ⟶ X` equals `U₀ ⟶ X₀ ⟶ X`, restricting `Y ×_X U` to `U₀` gives `Y₀ ×_{X₀} U₀`, which
the hypothesis identifies with `V ×_U U₀`; full faithfulness of restriction turns that
isomorphism over `U₀` into one over `U`. -/
@[sga "2 X 3.9" "(i)"]
private theorem exists_finiteEtale_extension_of_isEquivalence_of_fullyFaithful
    (S : LocalLefschetzSituation.{u})
    (hequiv : (finiteEtaleBaseChange S.X₀ToX).IsEquivalence)
    (hfull : Nonempty (finiteEtaleBaseChange S.U₀ToU).FullyFaithful)
    (V : Scheme.{u}) (pi : V ⟶ S.U) [IsFinite pi] [Etale pi]
    (Y₀ : Scheme.{u}) (f₀ : Y₀ ⟶ S.X₀) [IsFinite f₀] [Etale f₀]
    (g₀ : pullback pi S.U₀ToU ⟶ Y₀)
    (h₀ : IsPullback (pullback.snd pi S.U₀ToU) g₀ S.U₀Open.ι f₀) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ S.X) (g : V ⟶ Y),
      IsFinite p ∧ Etale p ∧ IsPullback pi g S.UOpen.ι p := by
  let : (finiteEtaleBaseChange S.X₀ToX).IsEquivalence := hequiv
  let E := finiteEtaleBaseChange S.X₀ToX
  let F := finiteEtaleBaseChange S.U₀ToU
  let G := finiteEtaleBaseChange S.UOpen.ι
  let J := finiteEtaleBaseChange S.U₀Open.ι
  let y₀ : FiniteEtaleOver S.X₀ :=
    MorphismProperty.Over.mk ⊤ f₀ ⟨inferInstance, inferInstance⟩
  let v : FiniteEtaleOver S.U :=
    MorphismProperty.Over.mk ⊤ pi ⟨inferInstance, inferInstance⟩
  obtain ⟨y, ⟨e₀⟩⟩ := Functor.EssSurj.mem_essImage (F := E) y₀
  let : F.Full := (Classical.choice hfull).full
  let : F.Faithful := (Classical.choice hfull).faithful
  let ecomp : G ⋙ F ≅ E ⋙ J :=
    (MorphismProperty.Over.pullbackComp
        (P := (finiteEtale : MorphismProperty Scheme.{u})) (Q := ⊤)
        S.U₀ToU S.UOpen.ι).symm ≪≫
      MorphismProperty.Over.pullbackCongr
          (P := (finiteEtale : MorphismProperty Scheme.{u})) (Q := ⊤)
          S.U₀ToU_comp_immersion ≪≫
        MorphismProperty.Over.pullbackComp
          (P := (finiteEtale : MorphismProperty Scheme.{u})) (Q := ⊤)
          S.U₀Open.ι S.X₀ToX
  let eV₀ : F.obj v ≅ J.obj y₀ := MorphismProperty.Over.isoMk
    (h₀.isoPullback ≪≫ pullbackSymmetry S.U₀Open.ι f₀) (by
      change (h₀.isoPullback ≪≫ pullbackSymmetry S.U₀Open.ι f₀).hom ≫
        pullback.snd f₀ S.U₀Open.ι = pullback.snd pi S.U₀ToU
      simpa only [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd] using
        h₀.isoPullback_hom_fst)
  let eVY : v ≅ G.obj y := F.preimageIso (eV₀ ≪≫ J.mapIso e₀.symm ≪≫ (ecomp.app y).symm)
  let eVYOver : Over.mk pi ≅ Over.mk (pullback.fst S.UOpen.ι y.hom) :=
    (MorphismProperty.Over.forget (finiteEtale : MorphismProperty Scheme.{u}) ⊤ S.U).mapIso
        eVY ≪≫
      Over.isoMk (pullbackSymmetry y.hom S.UOpen.ι) (by
        change (pullbackSymmetry y.hom S.UOpen.ι).hom ≫ pullback.fst S.UOpen.ι y.hom =
          pullback.snd y.hom S.UOpen.ι
        exact pullbackSymmetry_hom_comp_fst y.hom S.UOpen.ι)
  exact ⟨y.left, y.hom, eVYOver.hom.left ≫ pullback.snd S.UOpen.ι y.hom,
    y.prop.1, y.prop.2, IsPullback.of_over_iso eVYOver⟩

/-- The special case of [Stacks, Tag 0EK6] under hypothesis (c)(ii) where `A` is in addition
`f`-adically complete; the tag itself is `exists_finiteEtale_extension_of_dualizingComplex`. In
the local Lefschetz situation let `V` be finite étale over `U` and assume (a) `A` has a
dualizing complex `omega`, (b) the pair `(A, (f))` is henselian, (c)(ii)
`depth(A_𝔭) + dim(A/𝔭) > 2` for every prime `𝔭 ⊂ A` with `f ∉ 𝔭`, and (d) `V ×_U U₀` is
`Y₀ ×_{X₀} U₀` for some `Y₀ → X₀` finite étale. If moreover `A` is `f`-adically complete, then
`V = Y ×_X U` for some `Y → X` finite étale.

Hypothesis (b) is used twice: it is what Stacks 09ZS
(`finiteEtaleBaseChange_isEquivalence_of_henselianPair`) consumes to lift `Y₀` to a finite étale
`Y → X`, and it is hypothesis (b) of Stacks 0EK5.

The restrictions beyond the tag's own hypotheses are exactly those of this development's Stacks
0EK5 carrier `fullyFaithful_finiteEtaleRestriction_of_depth`, inherited unchanged: `A` is
`f`-adically complete (the source instead reduces to that case through Stacks 0BLL and Stacks
0ALZ/0EHW), only branch (ii) of hypothesis (c) is treated, and the three general hypotheses
`hEKP`, `h0GN2`, `halgebra` — statements about arbitrary Noetherian rings and arbitrary schemes,
none of them about `A`, `f`, `U`, `U₀` or finite étale covers of a punctured spectrum — are
granted. -/
public theorem exists_finiteEtale_extension_of_depth
    (S : LocalLefschetzSituation.{u})
    (hS : HenselianPair S.A S.principalIdeal)
    (omega : DerivedCategory (ModuleCat.{u} S.A))
    (homega : Dualizing.IsDualizingComplex (A := S.A) (K := omega))
    (hcomplete : IsAdicComplete (Ideal.span {S.f}) S.A)
    (hdepth : ∀ p : PrimeSpectrum S.A, S.f ∉ p.asIdeal →
      enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl S.A)) +
        krullDimToEInt (ringKrullDim (S.A ⧸ p.asIdeal)) > ((2 : ℤ) : EInt))
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
  exists_finiteEtale_extension_of_isEquivalence_of_fullyFaithful S
    (finiteEtaleBaseChange_isEquivalence_of_henselianPair S.A S.principalIdeal hS)
    (S.fullyFaithful_finiteEtaleRestriction_of_depth hS omega homega hcomplete hdepth hEKP
      h0GN2 halgebra)
    V pi Y₀ f₀ g₀ h₀

/-- The special case of [Stacks, Tag 0BLS] where `A` is in addition `f`-adically complete; the
tag itself is `exists_finiteEtale_extension_of_localCohomology_annihilated`. In the local
Lefschetz situation let `V` be finite étale over `U` and assume (1) `H¹_𝔪(A)` and
`H²_𝔪(A)` are annihilated by a power of `f`, and (2) `V ×_U U₀` is `Y₀ ×_{X₀} U₀` for some
`Y₀ → X₀` finite étale. If moreover `A` is `f`-adically complete, then `V = Y ×_X U` for some
`Y → X` finite étale.

The tag has no henselian hypothesis, and none is assumed: `(A, fA)` is a henselian pair because
`A` is `f`-adically complete, which is Stacks 0ALJ
(`henselianPair_of_isAdicComplete` above). That henselian pair feeds Stacks 09ZS, lifting `Y₀`
to a finite étale `Y → X`, and is also hypothesis (2) of Stacks 0BM6.

The restrictions beyond the tag's own hypotheses are exactly those of this development's Stacks
0BM6 carrier `fullyFaithful_finiteEtaleRestriction_of_annihilated`, inherited unchanged: `A` is
`f`-adically complete (the source instead reduces to that case, replacing `A` by its `𝔪`-adic
completion through Stacks 0BLL — available here as
`AlgebraicGeometry.exists_finiteEtale_extension_iff_completion` — and Stacks 0ALZ), and the
three general hypotheses `hEKP`, `h0GN2`, `halgebra` are granted. Those three are statements
about arbitrary Noetherian rings and arbitrary schemes; none is about `A`, `f`, `U`, `U₀` or
finite étale covers of a punctured spectrum. -/
public theorem exists_finiteEtale_extension_of_annihilated
    (S : LocalLefschetzSituation.{u})
    (hcomplete : IsAdicComplete (Ideal.span {S.f}) S.A)
    (h1 : ∃ n, ∀ x : localCohomologyModule S.A (maximalIdeal S.A)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal S.A)) (ModuleCat.of S.A S.A) 1,
      S.f ^ n • x = 0)
    (h2 : ∃ n, ∀ x : localCohomologyModule S.A (maximalIdeal S.A)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal S.A)) (ModuleCat.of S.A S.A) 2,
      S.f ^ n • x = 0)
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
      IsFinite p ∧ Etale p ∧ IsPullback pi g S.UOpen.ι p := by
  let : IsAdicComplete (Ideal.span {S.f}) S.A := hcomplete
  have hS : HenselianPair S.A S.principalIdeal :=
    henselianPair_of_isAdicComplete S.A (Ideal.span {S.f})
  exact exists_finiteEtale_extension_of_isEquivalence_of_fullyFaithful S
    (finiteEtaleBaseChange_isEquivalence_of_henselianPair S.A S.principalIdeal hS)
    (S.fullyFaithful_finiteEtaleRestriction_of_annihilated (Or.inr hS) hcomplete h1 h2 hEKP
      h0GN2 halgebra)
    V pi Y₀ f₀ g₀ h₀

end LocalLefschetzSituation

end AlgebraicGeometry

end
