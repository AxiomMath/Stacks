module

public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.AnnihilatedCriterion
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PuncturedSpectrumSectionsDepthTwo
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.PuncturedComplement
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionToClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TopologicalInvarianceFundamental.Basic
public import StacksFrontier.RingTheory.Henselian.Pair.Criteria

/-!
# Lifting a finite étale cover from the hypersurface section: the complete case

Work in the local Lefschetz situation of Tag 0BLF: `A` is a Noetherian local ring with maximal
ideal `𝔪`, `f ∈ 𝔪`, `X = Spec A`, `X₀ = Spec (A / fA)`, and `U`, `U₀` are the punctured spectra
of `A` and of `A / fA`. Assume that `A` is `f`-adically complete and that `H¹_𝔪(A)` and
`H²_𝔪(A)` are annihilated by a power of `f` (for instance, that `A` has depth at least `3`).

Then restriction `FÉt_U ⟶ FÉt_{U₀}` is fully faithful, and a finite étale `V ⟶ U` whose
restriction to `U₀` comes from a finite étale `Y₀ ⟶ X₀` comes from a finite étale `Y ⟶ X`.

## Main results

* `…LocalLefschetzSituation.fullyFaithful_finiteEtaleRestriction_of_isAdicComplete_of_annihilated`
  — full faithfulness of `FÉt_U ⟶ FÉt_{U₀}` for an `f`-adically complete `A` whose `H¹_𝔪(A)`
  and `H²_𝔪(A)` are annihilated by a power of `f`.
* `…LocalLefschetzSituation.exists_finiteEtale_extension_of_isAdicComplete_of_annihilated`
  — the lifting statement of Stacks 0BLS for an `f`-adically complete `A`.
* `…LocalLefschetzSituation.exists_finiteEtale_extension_of_isAdicComplete_of_three_le_depth`
  — the same lifting statement when `A` is `f`-adically complete of depth at least `3`.

## Implementation notes

Full faithfulness is Stacks 0EL8
(`…fullyFaithful_finiteEtaleBaseChange_of_completionFullyFaithfulOnFiniteLocallyFree`)
applied to the closed immersion `U₀ ⟶ U`, fed by Stacks 0EKS
(`Stacks.Algebraization.completionFullyFaithful_of_annihilated`). The two are matched by
`AlgebraicGeometry.LocalLefschetzSituation.UOpen_eq_complementZeroLocus` and
`AlgebraicGeometry.LocalLefschetzSituation.ker_U₀ToU`; since the scheme and the ideal sheaf both
move with the open, the open is generalized before the identification is substituted.

The lifting step is the source's argument: `(A, fA)` is a henselian pair because `A` is
`f`-adically complete, so base change along `X₀ ⟶ X` is an equivalence on finite étale covers
by Stacks 09ZS and `Y₀` lifts to some `Y ⟶ X`; full faithfulness then turns the isomorphism of
restrictions to `U₀` into an isomorphism `V ≅ Y ×_X U`.

Depth at least `3` gives the vanishing of `H¹_𝔪(A)` and `H²_𝔪(A)` through
`Stacks.LocalCohomology.subsingleton_localCohomologyModule_of_lt_depth` (Stacks 0AVZ).

## References

* [Stacks Project, Tag 0BLF](https://stacks.math.columbia.edu/tag/0BLF)
* [Stacks Project, Tag 0BLS](https://stacks.math.columbia.edu/tag/0BLS)
* [Stacks Project, Tag 0BM6](https://stacks.math.columbia.edu/tag/0BM6)
* [Stacks Project, Tag 0EKS](https://stacks.math.columbia.edu/tag/0EKS)
* [Stacks Project, Tag 0EL8](https://stacks.math.columbia.edu/tag/0EL8)
* [Stacks Project, Tag 09ZS](https://stacks.math.columbia.edu/tag/09ZS)
* [Stacks Project, Tag 0AVZ](https://stacks.math.columbia.edu/tag/0AVZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing
open Stacks.FundamentalGroup
open Stacks.LocalCohomology (complementZeroLocus localCohomologyModule)
open Stacks.Algebraization (CompletionFullyFaithfulOnFiniteLocallyFree)

universe u

namespace AlgebraicGeometry

namespace LocalLefschetzSituation

/-- In the local Lefschetz situation with `A` an `f`-adically complete ring whose `H¹_𝔪(A)` and
`H²_𝔪(A)` are annihilated by a power of `f`, restriction of finite étale covers
`FÉt_U ⟶ FÉt_{U₀}` is fully faithful. This is Stacks 0EKS followed by Stacks 0EL8. -/
theorem fullyFaithful_finiteEtaleRestriction_of_isAdicComplete_of_annihilated
    (S : LocalLefschetzSituation.{u})
    (hcomplete : IsAdicComplete (Ideal.span {S.f}) S.A)
    (h1 : ∃ n, ∀ x : localCohomologyModule S.A (maximalIdeal S.A)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal S.A)) (ModuleCat.of S.A S.A) 1,
      S.f ^ n • x = 0)
    (h2 : ∃ n, ∀ x : localCohomologyModule S.A (maximalIdeal S.A)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal S.A)) (ModuleCat.of S.A S.A) 2,
      S.f ^ n • x = 0) :
    Nonempty (finiteEtaleBaseChange S.U₀ToU).FullyFaithful := by
  have key : ∀ (W : (Spec (CommRingCat.of S.A)).Opens), W = S.UOpen →
      CompletionFullyFaithfulOnFiniteLocallyFree (W : Scheme)
        (Scheme.IdealSheafData.ofIdealTop (Ideal.span
          {((Scheme.ΓSpecIso (CommRingCat.of S.A)).inv ≫ W.ι.appTop).hom S.f})) →
      Nonempty (finiteEtaleBaseChange S.U₀ToU).FullyFaithful := by
    rintro W rfl hc
    rw [← S.ker_U₀ToU] at hc
    exact fullyFaithful_finiteEtaleBaseChange_of_completionFullyFaithfulOnFiniteLocallyFree
      S.U₀ToU hc
  exact key _ S.UOpen_eq_complementZeroLocus.symm
    (Stacks.Algebraization.completionFullyFaithful_of_annihilated S.A (maximalIdeal S.A) S.f
      S.f_mem_maximalIdeal hcomplete h1 h2)

/-- **Lifting from the hypersurface section, complete case (Stacks 0BLS).** In the local
Lefschetz situation let `A` be `f`-adically complete with `H¹_𝔪(A)` and `H²_𝔪(A)` annihilated by
a power of `f`. Let `V ⟶ U` be finite étale and suppose `V ×_U U₀ = Y₀ ×_{X₀} U₀` for some
finite étale `Y₀ ⟶ X₀`. Then `V = Y ×_X U` for some finite étale `Y ⟶ X`.

`(A, fA)` is a henselian pair since `A` is `f`-adically complete, so `Y₀` lifts to `Y ⟶ X` by
Stacks 09ZS; full faithfulness of `FÉt_U ⟶ FÉt_{U₀}` identifies `V` with `Y ×_X U`. -/
theorem exists_finiteEtale_extension_of_isAdicComplete_of_annihilated
    (S : LocalLefschetzSituation.{u})
    (hcomplete : IsAdicComplete (Ideal.span {S.f}) S.A)
    (h1 : ∃ n, ∀ x : localCohomologyModule S.A (maximalIdeal S.A)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal S.A)) (ModuleCat.of S.A S.A) 1,
      S.f ^ n • x = 0)
    (h2 : ∃ n, ∀ x : localCohomologyModule S.A (maximalIdeal S.A)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal S.A)) (ModuleCat.of S.A S.A) 2,
      S.f ^ n • x = 0)
    (V : Scheme.{u}) (pi : V ⟶ S.U) [IsFinite pi] [Etale pi]
    (Y₀ : Scheme.{u}) (f₀ : Y₀ ⟶ S.X₀) [IsFinite f₀] [Etale f₀]
    (g₀ : pullback pi S.U₀ToU ⟶ Y₀)
    (h₀ : IsPullback (pullback.snd pi S.U₀ToU) g₀ S.U₀Open.ι f₀) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ S.X) (g : V ⟶ Y),
      IsFinite p ∧ Etale p ∧ IsPullback pi g S.UOpen.ι p := by
  let : IsAdicComplete S.principalIdeal S.A := hcomplete
  let : HenselianRing S.A S.principalIdeal := IsAdicComplete.henselianRing S.A S.principalIdeal
  let : (finiteEtaleBaseChange S.X₀ToX).IsEquivalence :=
    finiteEtaleBaseChange_isEquivalence_of_henselianPair S.A S.principalIdeal
      (henselianPair_of_henselianRing S.A S.principalIdeal)
  have hfull := S.fullyFaithful_finiteEtaleRestriction_of_isAdicComplete_of_annihilated
    hcomplete h1 h2
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
      show (h₀.isoPullback ≪≫ pullbackSymmetry S.U₀Open.ι f₀).hom ≫
        pullback.snd f₀ S.U₀Open.ι = pullback.snd pi S.U₀ToU
      simpa only [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd] using
        h₀.isoPullback_hom_fst)
  let eVY : v ≅ G.obj y := F.preimageIso (eV₀ ≪≫ J.mapIso e₀.symm ≪≫ (ecomp.app y).symm)
  let eVYOver : Over.mk pi ≅ Over.mk (pullback.fst S.UOpen.ι y.hom) :=
    (MorphismProperty.Over.forget (finiteEtale : MorphismProperty Scheme.{u}) ⊤ S.U).mapIso
        eVY ≪≫
      Over.isoMk (pullbackSymmetry y.hom S.UOpen.ι) (by
        show (pullbackSymmetry y.hom S.UOpen.ι).hom ≫ pullback.fst S.UOpen.ι y.hom =
          pullback.snd y.hom S.UOpen.ι
        exact pullbackSymmetry_hom_comp_fst y.hom S.UOpen.ι)
  exact ⟨y.left, y.hom, eVYOver.hom.left ≫ pullback.snd S.UOpen.ι y.hom,
    y.prop.1, y.prop.2, IsPullback.of_over_iso eVYOver⟩

/-- **Lifting from the hypersurface section, complete case of depth at least three.** In the
local Lefschetz situation let `A` be `f`-adically complete of depth at least `3`. Let `V ⟶ U`
be finite étale and suppose `V ×_U U₀ = Y₀ ×_{X₀} U₀` for some finite étale `Y₀ ⟶ X₀`. Then
`V = Y ×_X U` for some finite étale `Y ⟶ X`.

Depth at least `3` makes `H¹_𝔪(A)` and `H²_𝔪(A)` vanish (Stacks 0AVZ), so
`exists_finiteEtale_extension_of_isAdicComplete_of_annihilated` applies. -/
theorem exists_finiteEtale_extension_of_isAdicComplete_of_three_le_depth
    (S : LocalLefschetzSituation.{u})
    (hdepth : 3 ≤ Module.depth S.A (maximalIdeal S.A) S.A)
    (hcomplete : IsAdicComplete (Ideal.span {S.f}) S.A)
    (V : Scheme.{u}) (pi : V ⟶ S.U) [IsFinite pi] [Etale pi]
    (Y₀ : Scheme.{u}) (f₀ : Y₀ ⟶ S.X₀) [IsFinite f₀] [Etale f₀]
    (g₀ : pullback pi S.U₀ToU ⟶ Y₀)
    (h₀ : IsPullback (pullback.snd pi S.U₀ToU) g₀ S.U₀Open.ι f₀) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ S.X) (g : V ⟶ Y),
      IsFinite p ∧ Etale p ∧ IsPullback pi g S.UOpen.ι p := by
  have hvanish : ∀ (i : ℕ) (j : ℤ), (i : ℤ) = j → i < 3 →
      ∃ n, ∀ x : localCohomologyModule S.A (maximalIdeal S.A)
        (Ideal.fg_of_isNoetherianRing (maximalIdeal S.A)) (ModuleCat.of S.A S.A) j,
        S.f ^ n • x = 0 := by
    rintro i j rfl hi
    have hlt : (i : ℕ∞) < Module.depth S.A (maximalIdeal S.A) S.A :=
      lt_of_lt_of_le (by exact_mod_cast hi) hdepth
    exact ⟨0, fun _ =>
      (Stacks.LocalCohomology.subsingleton_localCohomologyModule_of_lt_depth S.A
        (maximalIdeal S.A) (Ideal.fg_of_isNoetherianRing (maximalIdeal S.A))
        (ModuleCat.of S.A S.A) (by simpa using (maximalIdeal.isMaximal S.A).ne_top) i
        hlt).elim _ _⟩
  exact S.exists_finiteEtale_extension_of_isAdicComplete_of_annihilated hcomplete
    (hvanish 1 1 rfl (by norm_num)) (hvanish 2 2 rfl (by norm_num)) V pi Y₀ f₀ g₀ h₀

end LocalLefschetzSituation

end AlgebraicGeometry

end
