module

public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.ZariskisMainTheorem
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.JacobsonPuncturedSpectrum.Basic
public import StacksFrontier.RingTheory.EssentialFiniteness.Defs
public import StacksFrontier.RingTheory.EssentialFiniteness.ZariskiApplication
public import StacksFrontier.RingTheory.Noetherian.Spec

/-!
# A quasi-finite quotient near a point off the closed fibre

Let `A → B` be a local homomorphism of local rings which is essentially of finite type and has
finite residue-field extension, with `A` Noetherian. If an open subset of `Spec B` contains a
prime not lying over the maximal ideal of `A`, then it contains such a prime `q` for which the
quotient `B / q` is a localization of a finite-type quasi-finite `A`-algebra.

## Main results

* `Stacks.ClosedPointsFibre.exists_quotient_isLocalization_quasiFinite_of_isOpen`: an open of
  `Spec B` meeting the complement of the closed fibre contains a prime `q` off the closed fibre
  with `B / q` a localization of a finite-type quasi-finite `A`-algebra.

## References

* [Stacks Project, Tag 05GT](https://stacks.math.columbia.edu/tag/05GT)
-/

@[expose] public section

universe u

namespace Stacks.ClosedPointsFibre

/-- A quotient of a local ring by a proper ideal is local. -/
private theorem isLocalRing_quotient_of_ne_top {R : Type*} [CommRing R] [IsLocalRing R]
    {I : Ideal R} (hI : I ≠ ⊤) : IsLocalRing (R ⧸ I) :=
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective

/-- A prime ideal of the target of a surjective local homomorphism lying over the maximal ideal
is the maximal ideal. -/
private theorem eq_maximalIdeal_of_comap_eq_maximalIdeal {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (π : R →+* S) [IsLocalHom π]
    (hπ : Function.Surjective π) {p : Ideal S} (h : p.comap π = IsLocalRing.maximalIdeal R) :
    p = IsLocalRing.maximalIdeal S :=
  Ideal.comap_injective_of_surjective π hπ (h.trans (IsLocalRing.maximalIdeal_comap π).symm)

/-- An open of the spectrum of an essentially finite type local algebra which meets the
complement of the closed fibre contains a prime whose quotient is a localization of a
quasi-finite algebra. -/
@[stacks 05GT]
theorem exists_quotient_isLocalization_quasiFinite_of_isOpen
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A]
    (f : A →+* B) (hf : IsLocalHom f)
    (heft : IsEssentiallyOfFiniteType A B f)
    (hres : letI : IsLocalHom f := hf;
      letI := (IsLocalRing.ResidueField.map f).toAlgebra;
      Module.Finite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B))
    (V : Set (PrimeSpectrum B)) (hV : IsOpen V)
    (hne : ∃ q : PrimeSpectrum B,
      q ∈ V ∧ q.asIdeal.comap f ≠ IsLocalRing.maximalIdeal A) :
    ∃ q : PrimeSpectrum B, q ∈ V ∧
      q.asIdeal.comap f ≠ IsLocalRing.maximalIdeal A ∧
      letI := f.toAlgebra;
      ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C)
        (_ : Algebra.FiniteType A C) (_ : Algebra.QuasiFinite A C)
        (M : Submonoid C) (_ : Algebra C (B ⧸ q.asIdeal)),
        IsScalarTower A C (B ⧸ q.asIdeal) ∧ IsLocalization M (B ⧸ q.asIdeal) := by
  classical
  let : Algebra A B := f.toAlgebra
  obtain ⟨T, _, _, _, M, _, _, _⟩ := heft
  have : Algebra.EssFiniteType A T := Algebra.EssFiniteType.of_finiteType A T
  have : Algebra.EssFiniteType T B := Algebra.EssFiniteType.of_isLocalization B M
  have : Algebra.EssFiniteType A B := Algebra.EssFiniteType.comp A T B
  have : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing A B
  let U : Set (PrimeSpectrum B) := ({IsLocalRing.closedPoint B} : Set (PrimeSpectrum B))ᶜ
  have : JacobsonSpace ↥U := PrimeSpectrum.jacobsonSpace_compl_closedPoint B
  let W : Set U := {x | x.1 ∈ V ∧ x.1.asIdeal.comap f ≠ IsLocalRing.maximalIdeal A}
  have hWopen : IsOpen W := by
    have hclosed : IsClosed {x : PrimeSpectrum B |
        x.asIdeal.comap f = IsLocalRing.maximalIdeal A} := by
      convert (((PrimeSpectrum.isClosed_singleton_iff_isMaximal (IsLocalRing.closedPoint A)).2
        (IsLocalRing.maximalIdeal.isMaximal A)).preimage
          (PrimeSpectrum.continuous_comap f)) using 1
      ext x
      exact ⟨fun h ↦ PrimeSpectrum.ext h, fun h ↦ congrArg PrimeSpectrum.asIdeal h⟩
    change IsOpen (Subtype.val ⁻¹' (V ∩ {x : PrimeSpectrum B |
      x.asIdeal.comap f = IsLocalRing.maximalIdeal A}ᶜ))
    exact (hV.inter hclosed.isOpen_compl).preimage continuous_subtype_val
  have hWne : W.Nonempty := by
    obtain ⟨x, hxV, hxOver⟩ := hne
    have hxU : x ∈ U := by
      simp only [U, Set.mem_compl_iff, Set.mem_singleton_iff]
      rintro rfl
      exact hxOver (IsLocalRing.maximalIdeal_comap f)
    exact ⟨⟨x, hxU⟩, hxV, hxOver⟩
  obtain ⟨x, hxW, hxclosed⟩ :=
    nonempty_inter_closedPoints hWne hWopen.isLocallyClosed
  let q : Ideal B := x.1.asIdeal
  have hqprime : q.IsPrime := x.1.isPrime
  have hqnot : q.comap f ≠ IsLocalRing.maximalIdeal A := hxW.2
  let D := B ⧸ q
  let π : B →+* D := Ideal.Quotient.mk q
  let g : A →+* D := π.comp f
  have : IsLocalRing D := isLocalRing_quotient_of_ne_top hqprime.ne_top
  have : IsLocalHom π := IsLocalHom.of_surjective π Ideal.Quotient.mk_surjective
  let : Algebra A D := g.toAlgebra
  have : IsLocalHom g := RingHom.isLocalHom_comp π f
  have hresD :
      @Module.Finite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField D) _ _
        (Stacks.LocalizationOfFiniteAlgebra.residueAlgebra g).toModule := by
    have hrf : (IsLocalRing.ResidueField.map f).Finite := by
      let := (IsLocalRing.ResidueField.map f).toAlgebra
      exact hres
    have hsurj : Function.Surjective (IsLocalRing.ResidueField.map π) := by
      intro z
      obtain ⟨d, rfl⟩ := IsLocalRing.residue_surjective z
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective d
      exact ⟨IsLocalRing.residue B b, rfl⟩
    have hcomp : IsLocalRing.ResidueField.map g =
        (IsLocalRing.ResidueField.map π).comp (IsLocalRing.ResidueField.map f) :=
      IsLocalRing.ResidueField.map_comp f π
    have hrg : (IsLocalRing.ResidueField.map g).Finite := by
      rw [hcomp]
      exact (RingHom.Finite.of_surjective _ hsurj).comp hrf
    let : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField D) :=
      Stacks.LocalizationOfFiniteAlgebra.residueAlgebra g
    exact RingHom.finite_algebraMap.mp hrg
  have hftD : g.EssFiniteType := Algebra.instEssFiniteTypeQuotientIdeal A B q
  have hqSpecial : ∀ r : PrimeSpectrum B, q ≤ r.asIdeal →
      r ≠ IsLocalRing.closedPoint B → r.asIdeal = q := by
    intro r hqr hr
    have hrU : r ∈ U := by simp [U, hr]
    let y : U := ⟨r, hrU⟩
    have hspec : x ⤳ y := (subtype_specializes_iff _ _).mpr <|
      (PrimeSpectrum.le_iff_specializes x.1 r).mp ((PrimeSpectrum.asIdeal_le_asIdeal x.1 r).mp hqr)
    have hyx : y = x := by
      simpa [hxclosed.closure_eq] using specializes_iff_mem_closure.mp hspec
    simpa [q, y] using congrArg (fun z : U ↦ z.1.asIdeal) hyx
  have hspecD : ∀ p : PrimeSpectrum D,
      p.asIdeal = ⊥ ∨ p.asIdeal = IsLocalRing.maximalIdeal D := by
    intro p
    let r : PrimeSpectrum B := ⟨p.asIdeal.comap π, Ideal.IsPrime.comap _⟩
    have hqr : q ≤ r.asIdeal := Ideal.mk_ker.symm.le.trans (Ideal.ker_le_comap π)
    by_cases hr : r = IsLocalRing.closedPoint B
    · exact .inr (eq_maximalIdeal_of_comap_eq_maximalIdeal π Ideal.Quotient.mk_surjective
        (congrArg PrimeSpectrum.asIdeal hr))
    · refine .inl (Ideal.comap_injective_of_surjective π Ideal.Quotient.mk_surjective ?_)
      rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
      exact hqSpecial r hqr hr
  let J : Ideal D := Ideal.map g (IsLocalRing.maximalIdeal A)
  have hJle : J ≤ IsLocalRing.maximalIdeal D :=
    Ideal.map_le_iff_le_comap.mpr (IsLocalRing.maximalIdeal_comap g).ge
  have hJne : J ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal D).ne_top hJle
  have hJnotbot : J ≠ ⊥ := by
    intro h
    have hmap : Ideal.map g (IsLocalRing.maximalIdeal A) ≤ (⊥ : Ideal D) := by
      rw [← h]
    have hle : IsLocalRing.maximalIdeal A ≤ Ideal.comap g (⊥ : Ideal D) :=
      Ideal.map_le_iff_le_comap.mp hmap
    have hcomp : Ideal.comap g (⊥ : Ideal D) = q.comap f := by
      ext a
      change Ideal.Quotient.mk q (f a) = 0 ↔ f a ∈ q
      exact Ideal.Quotient.eq_zero_iff_mem
    have : (q.comap f).IsPrime := Ideal.IsPrime.comap f
    rw [hcomp] at hle
    exact hqnot (le_antisymm (IsLocalRing.le_maximalIdeal_of_isPrime (q.comap f)) hle)
  let F := D ⧸ J
  let ρ : D →+* F := Ideal.Quotient.mk J
  have : IsLocalRing F := isLocalRing_quotient_of_ne_top hJne
  have : IsLocalHom ρ := IsLocalHom.of_surjective ρ Ideal.Quotient.mk_surjective
  have hspecF : ∀ p : PrimeSpectrum F, p.asIdeal = IsLocalRing.maximalIdeal F := by
    intro p
    let r : PrimeSpectrum D := ⟨p.asIdeal.comap ρ, Ideal.IsPrime.comap _⟩
    have hJp : J ≤ r.asIdeal := Ideal.mk_ker.symm.le.trans (Ideal.ker_le_comap ρ)
    rcases hspecD r with hr | hr
    · exact absurd (le_antisymm (by simpa [hr] using hJp) bot_le) hJnotbot
    · exact eq_maximalIdeal_of_comap_eq_maximalIdeal ρ Ideal.Quotient.mk_surjective hr
  have : Subsingleton (PrimeSpectrum F) := ⟨fun p r ↦
    PrimeSpectrum.ext ((hspecF p).trans (hspecF r).symm)⟩
  have : T1Space (PrimeSpectrum F) := ⟨fun p ↦ by
    convert (isClosed_univ : IsClosed (Set.univ : Set (PrimeSpectrum F))) using 1
    ext r
    simp [Subsingleton.elim r p]⟩
  have : Finite (PrimeSpectrum F) := Finite.of_subsingleton
  have hdimLE : Ring.KrullDimLE 0 F :=
    (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp inferInstance).2
  have hdimD : ringKrullDim (Stacks.LocalizationOfFiniteAlgebra.closedFiber g) = 0 :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mp hdimLE
  obtain ⟨C, _, gC, hCD, N, hfinite, hcomp, hlocD⟩ :=
    Stacks.LocalizationOfFiniteAlgebra.essFiniteType_localization_finite g hftD hresD hdimD
  let : Algebra A C := gC.toAlgebra
  have : Module.Finite A C := hfinite
  let : Algebra C D := hCD.toAlgebra
  exact ⟨x.1, hxW.1, hqnot, C, inferInstance, inferInstance, inferInstance, inferInstance, N,
    hCD.toAlgebra, .of_algebraMap_eq' hcomp.symm, by simpa [D, q] using hlocD⟩

end Stacks.ClosedPointsFibre

end
