module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.Defs
public import StacksFrontier.RingTheory.Regular.Ideal
public import StacksFrontier.RingTheory.Regular.Quasiregular

/-!
# Finite projectivity of the conormal module of a presentation

For an algebra extension `P` of `S` over `R` with quasi-regular kernel, the conormal module
`P.Cotangent` is a finite projective `S`-module: this is Stacks 08RK for the ideal `P.ker`,
transported along the isomorphism `P.Ring ⧸ P.ker ≃+* S`. For a local complete intersection
the kernel of every finite polynomial presentation is Koszul-regular, hence quasi-regular,
so the conormal module of such a presentation is finite projective.
-/

@[expose] public section

namespace Algebra.Extension

/-- The conormal module of an extension with quasi-regular kernel is finite projective. -/
theorem cotangent_finite_projective_of_quasiregular {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (P : Algebra.Extension R S)
    (hP : Quasiregular.IsQuasiregularIdeal' P.ker) :
    Module.Finite S P.Cotangent ∧ Module.Projective S P.Cotangent := by
  obtain ⟨hfinite, hprojective⟩ :=
    Quasiregular.cotangent_finite_projective_of_quasiregular P.ker hP
  let e := (algebraMap P.Ring S).quotientKerEquivOfSurjective P.algebraMap_surjective
  have : RingHomInvPair e.toRingHom e.symm.toRingHom := .of_ringEquiv e
  have : RingHomInvPair e.symm.toRingHom e.toRingHom := .of_ringEquiv_symm e
  let E : P.ker.Cotangent ≃ₛₗ[e.toRingHom] P.Cotangent :=
    { P.cotangentEquivCotangentKer.symm.toAddEquiv with
      map_smul' r x := by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
        exact Cotangent.ext (Cotangent.val_smul' r (Cotangent.of x)).symm }
  exact ⟨Module.Finite.of_surjective E.toLinearMap E.surjective,
    Module.Projective.of_equiv E⟩

end Algebra.Extension

namespace Algebra.Generators

/-- For a local complete intersection, the conormal module of every finite polynomial
presentation is finite projective: the kernel of the presentation is Koszul-regular, hence
quasi-regular. -/
theorem cotangent_finite_projective_of_isLocalCompleteIntersection
    {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [Finite ι]
    (P : Algebra.Generators R S ι)
    (h : RingHom.IsLocalCompleteIntersection (algebraMap R S)) :
    Module.Finite S P.toExtension.Cotangent ∧
      Module.Projective S P.toExtension.Cotangent := by
  rw [RingHom.IsLocalCompleteIntersection, toAlgebra_algebraMap] at h
  obtain ⟨_, n, p, hp, hreg⟩ := h
  refine Extension.cotangent_finite_projective_of_quasiregular _
    (Ideal.IsKoszulRegular.isQuasiregular ?_)
  change Ideal.IsKoszulRegular P.ker
  rw [ker_eq_ker_aeval_val]
  exact RingHom.isKoszulRegularIdeal_ker_of_surjective_mvPolynomial
    p hp hreg (MvPolynomial.aeval P.val) P.aeval_val_surjective

end Algebra.Generators

end
