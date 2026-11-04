module

public import Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.RingTheory.Dualizing.DepthLemmas.Ext
public import StacksFrontier.RingTheory.Dualizing.LocalCohomologyNoetherian.UniverseChange
import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.DepthEqLocalCohomology

/-!
# Local cohomology below the depth, and the first stage above it

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `M` a finite `A`-module with `IM ≠ M`. The
`I`-depth of `M` is the least degree in which local cohomology supported on `V(I)` is nonzero —
the same number as the least degree in which `Ext_A(A/I, M)` is nonzero. The two halves of that
statement are proved here; the equality they combine into is
`Stacks.LocalCohomology.depth_eq_sInf_nontrivial_localCohomologyWithSupportIn` of
`StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.DepthEqLocalCohomology`.

## Main results

* `Stacks.LocalCohomology.subsingleton_localCohomologyWithSupportIn_of_lt_depth` — local
  cohomology vanishes below the depth.
* `Stacks.LocalCohomology.extPowers_map_succ_injective_of_depth` — in the degree equal to the
  depth, each transition map of the system `n ↦ Ext^d_A(A/I^n, M)` is injective, so nothing that
  appears there is later killed.

## Implementation notes

Both halves run through the identification of local cohomology with the filtered colimit of the
`Ext` modules from the quotients by the powers of `I` (Tag 0954), whose index set is `ℕ`. Below
the depth every stage of that system vanishes, because `A/I^n` is a finite module annihilated by
a power of `I`. In the degree equal to the depth the system need not be constant, which is what
makes the injectivity statement the thing to prove: the kernel of `A/I^{n+1} → A/I^n` is
annihilated by `I` and so has vanishing `Ext^{d-1}`.

The degrees of local cohomology are integers, those of depth natural numbers; the infimum is
taken in `ℕ∞`, where the infimum of the empty set is `⊤`, matching the convention of
`Module.depth`. A module of the large universe `max u v` is replaced throughout by its small
model, which `Module.Finite` provides and which changes neither the depth nor the local
cohomology.

## References

* [Stacks Project, Tag 0954](https://stacks.math.columbia.edu/tag/0954)
* [Stacks Project, Tag 0AVZ](https://stacks.math.columbia.edu/tag/0AVZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open Dualizing (localCohomology quotientPowerSucc extPowers)

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-- **Local cohomology vanishes below the depth.** For a finite module `M` over a Noetherian
ring with `IM ≠ M`, the local cohomology modules with support in `V(I)` vanish in every degree
below `depth_I(M)`. -/
@[sga "2 XII 1.5" "more general"]
theorem subsingleton_localCohomologyWithSupportIn_of_lt_depth (R : Type u) [CommRing R]
    [IsNoetherianRing R] (I : Ideal R) (M : ModuleCat.{max u v} R) [Module.Finite R M]
    (hIM : I • (⊤ : Submodule R M) ≠ ⊤) (i : ℕ) (hi : (i : ℕ∞) < Module.depth R I M) :
    Subsingleton (localCohomologyWithSupportIn R (PrimeSpectrum.zeroLocus (I : Set R))
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M) (i : ℤ)) := by
  have : Small.{u} (M : Type (max u v)) := Module.Finite.small.{u} R M
  let M₀ : ModuleCat.{u} R := ModuleCat.of R (Shrink.{u} (M : Type (max u v)))
  let eM : Shrink.{u} (M : Type (max u v)) ≃ₗ[R] (M : Type (max u v)) :=
    Shrink.linearEquiv R (M : Type (max u v))
  have : Module.Finite R (Shrink.{u} (M : Type (max u v))) := Module.Finite.equiv eM.symm
  have hIM₀ : I • (⊤ : Submodule R M₀) ≠ ⊤ := fun h => hIM ((eM.smul_top_eq_top_iff I).mp h)
  have hi₀ : (i : ℕ∞) < Module.depth R I (Shrink.{u} (M : Type (max u v))) := by
    simpa [Module.depth_eq_depth_of_linearEquiv I eM] using hi
  let K₀ := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M₀
  have hFzero : IsZero (extPowers R I K₀ (i : ℤ)) := by
    rw [Functor.isZero_iff]
    intro n
    apply ModuleCat.isZero_iff_subsingleton.mpr
    let Nₙ := ModuleCat.of R (R ⧸ I ^ n)
    have hExt : Subsingleton (Ext Nₙ M₀ i) :=
      ModuleCat.subsingleton_ext_of_lt_depth I M₀ Nₙ hIM₀ (k := n)
        (by rw [Ideal.annihilator_quotient]) hi₀
    have hDerived : Subsingleton (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj Nₙ) K₀ (i : ℤ)) :=
      ⟨fun x y => (Ext.homEquiv (X := Nₙ) (Y := M₀) (n := i)).symm.injective
        (hExt.elim _ _)⟩
    simpa [extPowers, Nₙ, DerivedCategory.Ext] using hDerived
  have hLift : IsZero ((ModuleCat.uliftFunctor.{u + 1} R).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i : ℤ)).obj
        (localCohomology R I K₀))) :=
    IsZero.of_iso ((colimit.isColimit _).isZero_pt hFzero)
      (localCohomologyHomologyIsoColimitExt R I K₀ (i : ℤ))
  have hL : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i : ℤ)).obj
      (localCohomology R I K₀)) :=
    (Equiv.ulift : ULift.{u + 1} _ ≃ _).subsingleton_congr.mp
      (ModuleCat.isZero_iff_subsingleton.mp hLift)
  exact ⟨fun x y =>
    (ModuleCat.mono_iff_injective (localCohomologyShrinkIso R I M (i : ℤ)).inv).mp
      inferInstance (((Equiv.ulift : ULift.{v} _ ≃ _).subsingleton_congr.mpr hL).elim _ _)⟩

/-- The transition map of the `Ext` system is precomposition with the quotient map
`R/I^{n+1} → R/I^n`. -/
private alias extPowers_map_succ_apply := DepthEq.extPowers_succ_apply

/-- The quotient map `R/I^{n+1} → R/I^n` is surjective. -/
private theorem quotientPowerSucc_surjective (R : Type u) [CommRing R] (I : Ideal R) (n : ℕ) :
    Function.Surjective (quotientPowerSucc R I n).hom := by
  intro y
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk (I ^ (n + 1)) r, by simp [quotientPowerSucc]⟩

/-- The kernel of the quotient map `R/I^{n+1} → R/I^n` is annihilated by `I`. -/
private theorem le_annihilator_ker_quotientPowerSucc (R : Type u) [CommRing R] (I : Ideal R)
    (n : ℕ) :
    I ≤ Module.annihilator R ((quotientPowerSucc R I n).hom.shortComplexKer.X₁ : Type u) := by
  intro a ha
  rw [Module.mem_annihilator]
  intro x
  obtain ⟨r, hrrep⟩ := Ideal.Quotient.mk_surjective (x.1 : R ⧸ I ^ (n + 1))
  have hr : r ∈ I ^ n := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hx := x.2
    rw [← hrrep] at hx
    simpa [quotientPowerSucc] using hx
  apply Subtype.ext
  show a • (x.1 : R ⧸ I ^ (n + 1)) = 0
  rw [← hrrep]
  show (Ideal.Quotient.mk (I ^ (n + 1)) a) * (Ideal.Quotient.mk (I ^ (n + 1)) r) = 0
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, pow_succ]
  simpa [mul_comm] using Ideal.mul_mem_mul hr ha

/-- If `depth_I(M) = d`, precomposition with the quotient map `R/I^{n+1} → R/I^n` is injective
on `Ext^d(-, M)`. -/
private theorem ext_precomp_quotientPowerSucc_injective (R : Type u) [CommRing R]
    [IsNoetherianRing R] (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M]
    (hIM : I • (⊤ : Submodule R M) ≠ ⊤) (d : ℕ) (hd : (d : ℕ∞) = Module.depth R I M) (n : ℕ) :
    Function.Injective (fun z : Ext (ModuleCat.of R (R ⧸ I ^ n)) M d =>
      (Ext.mk₀ (quotientPowerSucc R I n)).comp z (zero_add d)) := by
  let g := quotientPowerSucc R I n
  let S := g.hom.shortComplexKer
  have hsurj : Function.Surjective g.hom := quotientPowerSucc_surjective R I n
  have : Epi g := (ModuleCat.epi_iff_surjective g).mpr hsurj
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · exact Ext.precomp_mk₀_injective_of_epi M g
  have hdepth_lt : ((d - 1 : ℕ) : ℕ∞) < Module.depth R I M := by
    rw [← hd]
    exact_mod_cast Nat.sub_lt hd0 (by omega)
  have hkerExt : Subsingleton (Ext S.X₁ M (d - 1)) :=
    ModuleCat.subsingleton_ext_of_lt_depth I M S.X₁ hIM (k := 1)
      (by simpa using le_annihilator_ker_quotientPowerSucc R I n) hdepth_lt
  intro x y (hxy : (Ext.mk₀ g).comp x (zero_add d) = (Ext.mk₀ g).comp y (zero_add d))
  have hzero : (Ext.mk₀ g).comp (x - y) (zero_add d) = 0 := by
    simp [sub_eq_add_neg, hxy]
  obtain ⟨z, hz⟩ := Ext.contravariant_sequence_exact₃
    (LinearMap.shortExact_shortComplexKer hsurj : S.ShortExact) M (x - y) hzero
    (n₀ := d - 1) (by omega)
  exact sub_eq_zero.mp (by simpa [hkerExt.elim z 0] using hz.symm)

/-- **Nothing is killed in the degree equal to the depth.** If `depth_I(M) = d` then every
transition map of the system `n ↦ Ext^d_A(A/I^n, M)` is injective: the kernel of
`A/I^{n+1} → A/I^n` is annihilated by `I`, so its `Ext^{d-1}` into `M` vanishes and the
contravariant long exact sequence makes precomposition injective. -/
theorem extPowers_map_succ_injective_of_depth (R : Type u) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M]
    (hIM : I • (⊤ : Submodule R M) ≠ ⊤) (d : ℕ) (hd : (d : ℕ∞) = Module.depth R I M) (n : ℕ) :
    Function.Injective ((extPowers R I
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) (d : ℤ)).map
        (homOfLE (Nat.le_succ n))) := by
  let K := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M
  let F := extPowers R I K (d : ℤ)
  let Qₙ := ModuleCat.of R (R ⧸ I ^ n)
  let g := quotientPowerSucc R I n
  intro x y hxy
  change ShiftedHom ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj Qₙ)
    ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) (d : ℤ) at x y
  change F.map (homOfLE (Nat.le_succ n)) x = F.map (homOfLE (Nat.le_succ n)) y at hxy
  let eₙ := Ext.homEquiv (X := Qₙ) (Y := M) (n := d)
  let enext := Ext.homEquiv (X := ModuleCat.of R (R ⧸ I ^ (n + 1))) (Y := M) (n := d)
  have hnat (z : Ext Qₙ M d) :
      enext ((Ext.mk₀ g).comp z (zero_add d)) =
        (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map g ≫ eₙ z := by
    simpa [eₙ, enext, Ext.hom] using
      (Ext.singleFunctor_map_comp_hom (C := ModuleCat.{u} R) g z).symm
  have hcomp (z : F.obj n) : enext ((Ext.mk₀ g).comp (eₙ.symm z) (zero_add d)) =
      F.map (homOfLE (Nat.le_succ n)) z := by
    rw [hnat]
    erw [eₙ.apply_symm_apply]
    exact (extPowers_map_succ_apply R I K (d : ℤ) n z).symm
  refine eₙ.symm.injective
    (ext_precomp_quotientPowerSucc_injective R I M hIM d hd n (enext.injective ?_))
  rw [hcomp x, hcomp y]
  exact hxy

add_to_stacks 0AVZ "equality of depth and the first nonzero Ext degree"
  Module.depth_eq_sInf_nontrivial_ext

end Stacks.LocalCohomology

end
