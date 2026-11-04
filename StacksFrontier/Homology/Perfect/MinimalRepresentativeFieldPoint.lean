module

public import StacksFrontier.Homology.Perfect.MinimalRepresentative
public import StacksFrontier.Homology.Perfect.Saturation
public import StacksFrontier.Homology.ExtendScalars.DerivedHomology
public import StacksFrontier.Homology.TwoTermComplex.PresentationBaseChange

/-!
# Stacks 0BCD at a field-valued point

Let `R` be a commutative ring, `K` a perfect object of `D(R)` and `φ : R → L` a ring map to a
field. If the derived fibre `K ⊗ᴸ_R L` has no cohomology in degrees `< m`, then on a principal
open `D(f)` containing the point `ker φ` the object `K` is represented by a bounded complex of
finite projective modules concentrated in degrees `≥ m`.

This is the form of More on Algebra, Lemma 0BCD, used in the proof of Stacks 0DKY: the
hypothesis is read at an arbitrary field point (the residue field of a point of a chart is only
available up to a field extension), and the conclusion is read on any localization of `R` away
from `f` (the ring of functions of a basic open is a localization, not `Localization.Away f`
itself).

The field point `φ` factors through the residue field `κ(p)` of `p = ker φ`, and `κ(p) → L` is a
faithfully flat extension, so `K ⊗ᴸ κ(p)` has no cohomology below `m` either
(`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsHomologyIso`); the ranks of the
minimal representative of Stacks 0BCD
(`StacksDraft.Perfect.exists_away_bounded_free_complex_representing`) therefore vanish below `m`.

## Main results

* `StacksDraft.Perfect.isZero_homology_totalDerived_residueField_of_isZero`: vanishing of the
  cohomology of the derived fibre at a field point gives it at the residue field.
* `StacksDraft.Perfect.exists_isStrictlyGE_model_away_of_isGE_totalDerived_field`: the statement
  above.

## References

* [Stacks Project, Tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD)
* [Stacks Project, Tag 0DKY](https://stacks.math.columbia.edu/tag/0DKY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars

universe u

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

/-- **The cohomology of a derived fibre vanishes at the residue field as soon as it vanishes at
some field point.** Let `φ : R → L` be a ring map to a field, with kernel `p`, and `K` a perfect
object of `D(R)`. If `H^i(K ⊗ᴸ_R L) = 0` then `H^i(K ⊗ᴸ_R κ(p)) = 0`: `φ` factors through
`κ(p)` and `κ(p) → L` is faithfully flat. -/
theorem isZero_homology_totalDerived_residueField_of_isZero {R L : Type u} [CommRing R]
    [CommRing L] (hL : IsField L) (φ : R →+* L)
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : IsPerfect K) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} L) i).obj
      ((totalDerivedExtensionScalars.{u, u, u} φ).functor.obj K))) :
    haveI : (RingHom.ker φ).IsPrime := by
      let := hL.toField
      exact RingHom.ker_isPrime φ
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (RingHom.ker φ).ResidueField) i).obj
      ((totalDerivedExtensionScalars.{u, u, u}
        (algebraMap R (RingHom.ker φ).ResidueField)).functor.obj K)) := by
  let := hL.toField
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  let p := RingHom.ker φ
  have hunit : p.primeCompl ≤ Submonoid.comap φ (IsUnit.submonoid L) := fun x hx =>
    (IsUnit.mem_submonoid_iff _).2 ((isUnit_iff_ne_zero).2 fun h0 => hx (RingHom.mem_ker.2 h0))
  let ψ : p.ResidueField →+* L := Ideal.ResidueField.lift p φ le_rfl hunit
  have hcomp : ψ.comp (algebraMap R p.ResidueField) = φ :=
    RingHom.ext fun x => Ideal.ResidueField.lift_algebraMap _ _ _ hunit x
  obtain ⟨e⟩ := totalDerived_comp_of_isPseudoCoherent_of_eq.{u, u} hcomp
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap R p.ResidueField))
    (totalDerivedExtensionScalars.{u, u, u} ψ) (totalDerivedExtensionScalars.{u, u, u} φ)
    (isPseudoCoherent_of_isPerfect.{u, u} K hK)
  let : Algebra p.ResidueField L := ψ.toAlgebra
  have hflat : ψ.Flat := by
    show Module.Flat p.ResidueField L
    infer_instance
  let Y := (totalDerivedExtensionScalars.{u, u, u} (algebraMap R p.ResidueField)).functor.obj K
  have h₁ : IsZero ((ModuleCat.extendScalars.{u, u, u} ψ).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} p.ResidueField) i).obj Y)) :=
    (h.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e)).of_iso
      (derivedExtensionScalarsHomologyIso.{u, u, u} ψ hflat Y i).symm
  rw [ModuleCat.isZero_iff_subsingleton] at h₁ ⊢
  exact (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right p.ResidueField L).1 h₁

/-- **Stacks 0BCD at a field point, read on any localization.** Let `R` be a commutative ring,
`K` a perfect object of `D(R)` and `φ : R → L` a ring map to a field such that `K ⊗ᴸ_R L` lies in
`D^{≥ m}`. Then there is `f ∈ R` with `φ(f) ≠ 0` such that for every localization `S'` of `R`
away from `f`, `K ⊗ᴸ_R S'` is represented by a bounded complex of finite projective
`S'`-modules concentrated in degrees `≥ m`. -/
theorem exists_isStrictlyGE_model_away_of_isGE_totalDerived_field {R L : Type u} [CommRing R]
    [CommRing L] (hL : IsField L) (φ : R →+* L)
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : IsPerfect K) (m : ℤ)
    (hφ : ((totalDerivedExtensionScalars.{u, u, u} φ).functor.obj K).IsGE m) :
    ∃ f : R, f ∉ RingHom.ker φ ∧
      ∀ (S' : Type u) [CommRing S'] [Algebra R S'] [IsLocalization.Away f S'],
        ∃ (P : CochainComplex (ModuleCat.{u} S') ℤ) (b : ℤ),
          P.IsStrictlyGE m ∧ P.IsStrictlyLE b ∧
            (∀ i, Module.Finite S' (P.X i)) ∧ (∀ i, Module.Projective S' (P.X i)) ∧
            Nonempty (DerivedCategory.Q.obj P ≅
              (totalDerivedExtensionScalars.{u, u, u} (algebraMap R S')).functor.obj K) := by
  let := hL.toField
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  let p := RingHom.ker φ
  obtain ⟨-, -, f, hf, P, a, b, -, hb, hPX, ⟨eP⟩⟩ :=
    exists_away_bounded_free_complex_representing.{u, u} p K hK
  have hX : ∀ i, Module.Finite (Localization.Away f) (P.X i) ∧
      Module.Projective (Localization.Away f) (P.X i) := fun i =>
    let e := (ULift.moduleEquiv).symm ≪≫ₗ (hPX i).some.toLinearEquiv.symm
    ⟨Module.Finite.equiv e, Module.Projective.of_equiv e⟩
  have hge : P.IsStrictlyGE m := by
    refine (CochainComplex.isStrictlyGE_iff P m).2 fun i hi => ?_
    have h0 := isZero_homology_totalDerived_residueField_of_isZero hL φ K hK i
      (DerivedCategory.isZero_of_isGE _ m i hi)
    have hr : Module.finrank p.ResidueField ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} p.ResidueField) i).obj ((totalDerivedExtensionScalars.{u, u, u}
          (algebraMap R p.ResidueField)).functor.obj K)) = 0 := by
      rw [ModuleCat.isZero_iff_subsingleton] at h0
      exact Module.finrank_zero_of_subsingleton
    refine IsZero.of_iso ?_ (hPX i).some
    rw [ModuleCat.isZero_iff_subsingleton]
    simp only [hr]
    infer_instance
  refine ⟨f, hf, fun S' _ _ _ => ?_⟩
  let e : Localization.Away f ≃ₐ[R] S' :=
    IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f) S'
  let ε : Localization.Away f →+* S' := e.toAlgHom.toRingHom
  have hcomp : ε.comp (algebraMap R (Localization.Away f)) = algebraMap R S' :=
    RingHom.ext fun x => e.commutes x
  obtain ⟨c⟩ := totalDerived_comp_of_isPseudoCoherent_of_eq.{u, u} hcomp
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap R (Localization.Away f)))
    (totalDerivedExtensionScalars.{u, u, u} ε) (totalDerivedExtensionScalars.{u, u, u}
      (algebraMap R S')) (isPseudoCoherent_of_isPerfect.{u, u} K hK)
  let ext := ModuleCat.extendScalars.{u, u, u} ε
  have : ext.Additive := extendScalars_additive.{u, u} _
  have := hb
  have : ∀ i, Projective (P.X i) := fun i => by have := (hX i).2; infer_instance
  have := (totalDerivedExtensionScalars.{u, u, u} ε).comparison_isIso_of_projective P b
  refine ⟨(ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj P, b, ?_, ?_, fun i => ?_,
    fun i => ?_, ⟨?_⟩⟩
  · exact (CochainComplex.isStrictlyGE_iff _ m).2 fun i hi =>
      ext.map_isZero (P.isZero_of_isStrictlyGE m i hi)
  · exact (CochainComplex.isStrictlyLE_iff _ b).2 fun i hi =>
      ext.map_isZero (P.isZero_of_isStrictlyLE b i hi)
  · have := (hX i).1
    exact TwoTermDeterminant.finite_extendScalars ε (P.X i)
  · have := (hX i).2
    exact TwoTermDeterminant.projective_extendScalars ε (P.X i)
  · exact (asIso ((totalDerivedExtensionScalars.{u, u, u} ε).comparison.app P)).symm ≪≫
      (totalDerivedExtensionScalars.{u, u, u} ε).functor.mapIso eP ≪≫ c

end StacksDraft.Perfect

end
