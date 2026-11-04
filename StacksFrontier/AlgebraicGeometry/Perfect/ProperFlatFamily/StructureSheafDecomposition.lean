module

public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.Support
import StacksCore.Tactic.StacksAttribute

/-!
# Finite etaleness spread out from one point

Let `R` be a commutative ring, `p ⊂ R` a prime and `A` a finite free `R`-algebra. If the fibre
`κ(p) ⊗_R A` is etale over `κ(p)`, then `R_h ⊗_R A` is finite etale over `R_h` for every `h` in
some basic open neighbourhood of `p`. This is the affine-local algebraic form of the finite
etaleness of `f_*𝒪_X` near a point `s` in [Stacks, Tag 0G7Y], obtained through the openness of
the etale locus [Stacks, Tag 0476].

## Main results

* `etale_of_isReduced_of_isSeparable_residueFields`: a module-finite reduced algebra over a field
  whose residue fields are separable is finite etale.
* `exists_away_finiteEtale_of_unramified_fibre`: for `A` a finite free `R`-algebra whose fibre
  `κ(p) ⊗_R A` is formally unramified over `κ(p)`, there is `g ∉ p` such that for every `h`
  divisible by `g` the algebra `R_h ⊗_R A` is finite free and etale over `R_h`.
* `exists_away_finiteEtale_of_isReduced_fibre`: the same conclusion when the fibre is reduced with
  separable residue fields.

## Implementation notes

The openness of the etale locus is expressed through the module of Kahler differentials:

1. `Ω[A⁄R]` is a finite `A`-module because `A` is of finite type over `R`, hence a finite
   `R`-module because `A` is a finite `R`-module.
2. Kahler differentials commute with arbitrary base change
   (`KaehlerDifferential.tensorKaehlerEquivBase`), so the hypothesis on the fibre says exactly
   that `κ(p) ⊗_R Ω[A⁄R]` vanishes.
3. For a finite module that is the statement that `p` is outside the support
   (`Module.mem_support_iff_nontrivial_residueField_tensorProduct`), so the localization of
   `Ω[A⁄R]` at `p` vanishes, and the support being closed there is a single `g ∉ p` with
   `Ω[A⁄R][1/g] = 0` (`LocalizedModule.exists_subsingleton_away`). Every `h` divisible by `g`
   inherits this, because the zero locus of `g` is contained in that of `h`.
4. Base change again turns `Ω[A⁄R][1/h] = 0` into `Ω[(R_h ⊗_R A)⁄R_h] = 0`, i.e. `R_h ⊗_R A` is
   formally unramified over `R_h`.
5. A finite free algebra is finitely presented as a module, hence as an algebra, and flat; so
   `R_h ⊗_R A` is flat and of finite presentation over `R_h`, and flat plus formally unramified
   plus of finite presentation is etale ([Stacks, Tag 08WD],
   `Algebra.Etale.of_formallyUnramified_of_flat`).

The fibre condition of [Stacks, Tag 0BUG] (3) and (4) is turned into etaleness as follows: a
module-finite algebra over a field is Artinian, an Artinian reduced ring is the product of its
residue fields (`IsArtinianRing.equivPi`), and an etale algebra over a field is a finite product
of finite separable field extensions (`Algebra.Etale.iff_exists_algEquiv_prod`).

## References

* [Stacks Project, Tag 0G7Y](https://stacks.math.columbia.edu/tag/0G7Y)
* [Stacks Project, Tag 0476](https://stacks.math.columbia.edu/tag/0476)
* [Stacks Project, Tag 08WD](https://stacks.math.columbia.edu/tag/08WD)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
-/

@[expose] public section

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] IsArtinianRing.fieldOfSubtypeIsMaximal

namespace Stacks.AlgebraicGeometry.ProperFlatStructureSheaf

universe u v

/-- The zero locus of `g` is contained in the zero locus of any multiple of `g`. -/
private theorem zeroLocus_singleton_subset_of_dvd {R : Type u} [CommRing R] {g h : R}
    (hgh : g ∣ h) :
    PrimeSpectrum.zeroLocus ({g} : Set R) ⊆ PrimeSpectrum.zeroLocus ({h} : Set R) := by
  obtain ⟨k, rfl⟩ := hgh
  intro x hx
  simp only [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe] at hx ⊢
  exact Ideal.mul_mem_right k _ hx

/-- If a module dies after inverting `g`, it dies after inverting any multiple of `g`. -/
private theorem subsingleton_away_of_dvd {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M]
    [Module R M] {g h : R} (hgh : g ∣ h) [Subsingleton (LocalizedModule.Away g M)] :
    Subsingleton (LocalizedModule.Away h M) :=
  LocalizedModule.subsingleton_iff_support_subset.mpr
    (LocalizedModule.subsingleton_iff_support_subset.mp ‹_› |>.trans
      (zeroLocus_singleton_subset_of_dvd hgh))

/-- Let `R` be a commutative ring, `p ⊂ R` a prime and `A` a finite free `R`-algebra whose fibre
`κ(p) ⊗_R A` is formally unramified over `κ(p)`. Then there is `g ∈ R` outside `p` such that for
every `h` divisible by `g` the algebra `R_h ⊗_R A` is a finite free and etale `R_h`-algebra. -/
theorem exists_away_finiteEtale_of_unramified_fibre {R : Type u} [CommRing R] (p : Ideal R)
    [p.IsPrime] (A : Type v) [CommRing A] [Algebra R A] [Module.Finite R A] [Module.Free R A]
    (hfib : Algebra.FormallyUnramified p.ResidueField (p.Fiber A)) :
    ∃ g : R, g ∉ p ∧ ∀ h : R, g ∣ h →
      Module.Finite (Localization.Away h) (Localization.Away h ⊗[R] A) ∧
        Module.Free (Localization.Away h) (Localization.Away h ⊗[R] A) ∧
        Algebra.Etale (Localization.Away h) (Localization.Away h ⊗[R] A) := by
  have hmod : Module.FinitePresentation R A := Module.finitePresentation_of_projective R A
  have halg : Algebra.FinitePresentation R A :=
    Algebra.FinitePresentation.of_finitePresentation R A
  have hΩR : Module.Finite R Ω[A⁄R] := Module.Finite.trans A _
  have hfibΩ : Subsingleton Ω[(p.Fiber A)⁄p.ResidueField] :=
    (Algebra.formallyUnramified_iff _ _).mp hfib
  have hres : Subsingleton (p.ResidueField ⊗[R] Ω[A⁄R]) :=
    (KaehlerDifferential.tensorKaehlerEquivBase R p.ResidueField A
      (p.Fiber A)).toEquiv.subsingleton
  have hnotmem : (⟨p, ‹p.IsPrime›⟩ : PrimeSpectrum R) ∉ Module.support R Ω[A⁄R] := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
    exact not_nontrivial_iff_subsingleton.mpr hres
  have hloc : Subsingleton (LocalizedModule p.primeCompl Ω[A⁄R]) :=
    Module.notMem_support_iff.mp hnotmem
  obtain ⟨g, hg, hgsub⟩ := LocalizedModule.exists_subsingleton_away (M := Ω[A⁄R]) p
  refine ⟨g, hg, fun h hgh => ⟨inferInstance, inferInstance, ?_⟩⟩
  have hhsub : Subsingleton (LocalizedModule.Away h Ω[A⁄R]) := subsingleton_away_of_dvd hgh
  have hAway : Subsingleton (Localization.Away h ⊗[R] Ω[A⁄R]) :=
    (LocalizedModule.equivTensorProduct (Submonoid.powers h) Ω[A⁄R]).symm.toEquiv.subsingleton
  have hΩh : Subsingleton Ω[(Localization.Away h ⊗[R] A)⁄Localization.Away h] :=
    (KaehlerDifferential.tensorKaehlerEquivBase R (Localization.Away h) A
      (Localization.Away h ⊗[R] A)).symm.toEquiv.subsingleton
  have hunr : Algebra.FormallyUnramified (Localization.Away h) (Localization.Away h ⊗[R] A) :=
    (Algebra.formallyUnramified_iff _ _).mpr hΩh
  have hfp : Algebra.FinitePresentation (Localization.Away h) (Localization.Away h ⊗[R] A) :=
    inferInstance
  exact Algebra.Etale.of_formallyUnramified_of_flat

/-- A module-finite reduced algebra over a field `k`, each of whose residue fields at maximal
ideals is separable over `k`, is etale over `k`. -/
@[ega "IV 17.6.1" "c′ ⇒ a over a field base",
  ega "IV 18.2.3" "special case",
  ega "IV 18.3.3" "partial",
  sga "1 IX 1.8" "converse direction",
  sga "3 VIIB 1.6.E" "(a), special case",
  sga "4½ Arcata 2.1.2" "partial",
  sga "4½ Arcata 2.4.2" "converse"]
theorem etale_of_isReduced_of_isSeparable_residueFields (k : Type u) [Field k] (A : Type v)
    [CommRing A] [Algebra k A] [Module.Finite k A] [IsReduced A]
    (hsep : ∀ i : MaximalSpectrum A, Algebra.IsSeparable k (A ⧸ i.asIdeal)) :
    Algebra.Etale k A := by
  have : IsArtinianRing A := isArtinian_of_tower k inferInstance
  refine (Algebra.Etale.iff_exists_algEquiv_prod k A).mpr
    ⟨MaximalSpectrum A, inferInstance, fun i => A ⧸ i.asIdeal, inferInstance, inferInstance,
      (IsArtinianRing.equivPi A).restrictScalars k, fun i => ⟨?_, hsep i⟩⟩
  exact Module.Finite.of_surjective (Ideal.Quotient.mkₐ k i.asIdeal).toLinearMap
    Ideal.Quotient.mk_surjective

/-- Let `R` be a commutative ring, `p ⊂ R` a prime and `A` a finite free `R`-algebra whose fibre
`κ(p) ⊗_R A` is reduced, with each of its residue fields at maximal ideals separable over `κ(p)`.
Then there is `g ∈ R` outside `p` such that for every `h` divisible by `g` the algebra
`R_h ⊗_R A` is a finite free and etale `R_h`-algebra. -/
theorem exists_away_finiteEtale_of_isReduced_fibre {R : Type u} [CommRing R] (p : Ideal R)
    [p.IsPrime] (A : Type v) [CommRing A] [Algebra R A] [Module.Finite R A] [Module.Free R A]
    [IsReduced (p.Fiber A)]
    (hsep : ∀ i : MaximalSpectrum (p.Fiber A),
      Algebra.IsSeparable p.ResidueField (p.Fiber A ⧸ i.asIdeal)) :
    ∃ g : R, g ∉ p ∧ ∀ h : R, g ∣ h →
      Module.Finite (Localization.Away h) (Localization.Away h ⊗[R] A) ∧
        Module.Free (Localization.Away h) (Localization.Away h ⊗[R] A) ∧
        Algebra.Etale (Localization.Away h) (Localization.Away h ⊗[R] A) :=
  have : Algebra.Etale p.ResidueField (p.Fiber A) :=
    etale_of_isReduced_of_isSeparable_residueFields p.ResidueField (p.Fiber A) hsep
  exists_away_finiteEtale_of_unramified_fibre p A inferInstance

end Stacks.AlgebraicGeometry.ProperFlatStructureSheaf

end
