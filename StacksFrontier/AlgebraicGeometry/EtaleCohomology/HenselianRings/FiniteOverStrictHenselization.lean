module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.FiniteBaseChangeStrictHenselization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictlyHenselianFiniteAlgebras
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite morphisms over a strictly henselian local scheme

A finite scheme over the spectrum of a strictly henselian local ring is a finite disjoint union
of spectra of strictly henselian local rings, each finite over the base. Since the étale local
ring of a scheme at a geometric point is strictly henselian
(`AlgebraicGeometry.etaleLocalRing_strictHenselian`), this applies to the base change of a
finite morphism to the strict henselization at a geometric point of the target; that
decomposition, with components indexed by the lifts of the geometric point, is
`AlgebraicGeometry.finite_baseChange_strictHenselization_decomposition`.

## Main results

* `AlgebraicGeometry.exists_finite_coproduct_strictHenselian_of_finite`: a finite scheme over
  the spectrum of a strictly henselian local ring is a finite coproduct of spectra of strictly
  henselian local rings.

## References

* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

/-- A finite scheme over the spectrum of a strictly henselian local ring is a finite coproduct
of spectra of strictly henselian local rings, each finite over the base. -/
@[sga "4 VIII 5.4"]
theorem exists_finite_coproduct_strictHenselian_of_finite
    (R : Type u) [CommRing R] [_root_.StrictlyHenselianLocalRing R]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of R)) [IsFinite f] :
    ∃ (ι : Type u) (_ : Finite ι) (B : ι → Type u)
      (_ : ∀ i, CommRing (B i))
      (_ : ∀ i, Algebra (Γ(Spec (.of R), ⊤)) (B i))
      (_ : ∀ i, _root_.StrictlyHenselianLocalRing (B i)),
      (∀ i, Module.Finite (Γ(Spec (.of R), ⊤)) (B i)) ∧
      Nonempty ((∐ fun i : ι => Spec (.of (B i))) ≅ X) := by
  let P := Γ(Spec (.of R), ⊤)
  let eP : P ≃+* R := (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
  let : IsLocalRing P := eP.symm.isLocalRing
  let : _root_.StrictlyHenselianLocalRing P := strictlyHenselianLocalRing_of_ringEquiv eP.symm
  let A := Γ(X, ⊤)
  let : IsAffine X := isAffine_of_isAffineHom f
  let : Algebra P A := f.appTop.hom.toAlgebra
  have hfinite : Module.Finite P A := by
    rw [← RingHom.finite_algebraMap]
    exact IsFinite.finite_app f ⊤ (isAffineOpen_top _)
  obtain ⟨ι, hι, B, hBcomm, hBalg, hBstrict, hBfinite, ⟨e⟩⟩ :=
    exists_algEquiv_pi_strictHenselian_of_module_finite P A
  exact ⟨ι, hι, B, hBcomm, hBalg, hBstrict, hBfinite,
    ⟨asIso (sigmaSpec fun i ↦ CommRingCat.of (B i)) ≪≫
      Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op ≪≫ X.isoSpec.symm⟩⟩

end AlgebraicGeometry

end
