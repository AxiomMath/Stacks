module

public import StacksFrontier.AlgebraicGeometry.TwoAffineCech.Fibre
public import StacksFrontier.Algebra.Module.TwoTermComplex.Model
public import StacksFrontier.AlgebraicGeometry.TwoAffineCech.FibreDims

/-!
# Cohomology and base change over a Noetherian affine base, for two-affine coverings

Let `A` be a Noetherian ring, `f : X ⟶ Spec A` proper and separated, `U` a covering of `X` by two
affine opens, and `F` a coherent `𝒪_X`-module flat over `A`. For a point `p` of `Spec A` write
`X_p` for the fibre, the base change along `Spec κ(p) ⟶ Spec A`, and `F_p` for the pullback of `F`.
Then the two-term Čech differential of `F` has a finite projective model, so:

* the locus of `p` with `H¹(X_p, F_p) = 0` and `dim H⁰(X_p, F_p) = r` is open;
* the fibre Euler characteristic `p ↦ dim H⁰(X_p, F_p) - dim H¹(X_p, F_p)` is locally constant.

This is the two-term case of [Stacks, Tag 0BDJ] and [Stacks, Tag 0BDK] for `Rf_*F`, proved
directly on the Čech complex; no `@[stacks]` attribute is attached because the tags are stated
for perfect complexes.

## Main definitions

* `Stacks.TwoAffineCech.fibre`, `fibreProj`, `fibreMap`: the canonical fibre of `X` over a point.

## Main results

* `Stacks.TwoAffineCech.isOpen_setOf_fibre_cohomology`.
* `Stacks.TwoAffineCech.isLocallyConstant_fibre_euler`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Stacks.TwoAffineCech

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- The residue map at a point of the spectrum. -/
abbrev residueMap (p : PrimeSpectrum A) : A →+* p.asIdeal.ResidueField :=
  algebraMap A p.asIdeal.ResidueField

/-- The algebra structure induced by the residue map is the canonical one. -/
theorem toAlgebra_residueMap (p : PrimeSpectrum A) :
    (residueMap p).toAlgebra = (inferInstance : Algebra A p.asIdeal.ResidueField) :=
  Algebra.algebra_ext _ _ fun _ => rfl

/-- The fibre of `X` over a point of `Spec A`. -/
abbrev fibre (p : PrimeSpectrum A) : Scheme.{u} :=
  pullback f (Spec.map (CommRingCat.ofHom (residueMap p)))

/-- The projection of the fibre onto `X`. -/
abbrev fibreMap (p : PrimeSpectrum A) : fibre f p ⟶ X := pullback.fst _ _

/-- The structure morphism of the fibre to `Spec κ(p)`. -/
abbrev fibreProj (p : PrimeSpectrum A) : fibre f p ⟶ Spec (.of p.asIdeal.ResidueField) :=
  pullback.snd _ _

/-- The fibre of `X` over `p` is the pullback of `f` along `Spec κ(p) ⟶ Spec A`. -/
theorem isPullback_fibre (p : PrimeSpectrum A) :
    IsPullback (fibreMap f p) (fibreProj f p) f (Spec.map (CommRingCat.ofHom (residueMap p))) :=
  IsPullback.of_hasPullback _ _

variable (U : Cover.{u} → X.Opens) (F : X.Modules) [IsSeparated f] [F.IsQuasicoherent]
  (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))

/-- `H¹` of the fibre is the cokernel of the fibre of the Čech differential, for the canonical
algebra structure on the residue field. -/
private def cohomologyOverFieldOneEquiv' (hU : (⊤ : X.Opens) = ⨆ i, U i)
    (hUaff : ∀ i, IsAffineOpen (U i)) (p : PrimeSpectrum A) :
    cohomologyOverField p.asIdeal.ResidueField (fibreProj f p)
        ((Scheme.Modules.pullback (fibreMap f p)).obj F) 1 ≃ₗ[p.asIdeal.ResidueField]
      (p.asIdeal.ResidueField ⊗[A] (Stacks.Cech.alternatingCechModuleComplex f U F).X 1 ⧸
        LinearMap.range ((cechD f U F).baseChange p.asIdeal.ResidueField)) := by
  have e := cohomologyOverFieldOneEquiv (residueMap p) f (fibreProj f p) (fibreMap f p)
      (isPullback_fibre f p) U F hU hUaff
  rw [toAlgebra_residueMap] at e
  exact e

include hU hUaff in
/-- `H¹` of the fibre vanishes exactly when the fibre of the Čech differential is onto. -/
theorem isZero_cohomologyOverField_one_iff (p : PrimeSpectrum A) :
    IsZero (cohomologyOverField p.asIdeal.ResidueField (fibreProj f p)
        ((Scheme.Modules.pullback (fibreMap f p)).obj F) 1) ↔
      Function.Surjective ((cechD f U F).baseChange p.asIdeal.ResidueField) := by
  rw [ModuleCat.isZero_iff_subsingleton,
    (cohomologyOverFieldOneEquiv' f U F hU hUaff p).toEquiv.subsingleton_congr,
    Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top]

include hU hUaff in
/-- `dim H⁰` of the fibre is the dimension of the kernel of the fibre of the Čech differential. -/
theorem finrank_cohomologyOverField_zero_eq (p : PrimeSpectrum A) :
    Module.finrank p.asIdeal.ResidueField (cohomologyOverField p.asIdeal.ResidueField
        (fibreProj f p) ((Scheme.Modules.pullback (fibreMap f p)).obj F) 0) =
      Module.finrank p.asIdeal.ResidueField
        (LinearMap.ker ((cechD f U F).baseChange p.asIdeal.ResidueField)) := by
  have e := cohomologyOverFieldZeroEquiv (residueMap p) f (fibreProj f p) (fibreMap f p)
      (isPullback_fibre f p) U F hU hUaff
  rw [toAlgebra_residueMap] at e
  exact e.finrank_eq

include hU hUaff in
/-- `dim H¹` of the fibre is the dimension of the cokernel of the fibre of the Čech
differential. -/
theorem finrank_cohomologyOverField_one_eq (p : PrimeSpectrum A) :
    Module.finrank p.asIdeal.ResidueField (cohomologyOverField p.asIdeal.ResidueField
        (fibreProj f p) ((Scheme.Modules.pullback (fibreMap f p)).obj F) 1) =
      Module.finrank p.asIdeal.ResidueField
        (p.asIdeal.ResidueField ⊗[A] (Stacks.Cech.alternatingCechModuleComplex f U F).X 1 ⧸
          LinearMap.range ((cechD f U F).baseChange p.asIdeal.ResidueField)) := by
  exact (cohomologyOverFieldOneEquiv' f U F hU hUaff p).finrank_eq

omit [IsSeparated f] in
include hU hUaff in
/-- Over a Noetherian base, for `f` proper and `F` coherent and flat, the two-term Čech
differential has a finite projective model. -/
theorem hasFiniteProjectiveModel [IsNoetherianRing A] [IsProper f] [F.IsCoherent]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    Stacks.TwoTermComplex.HasFiniteProjectiveModel (cechD f U F) :=
  have := flat_X f U F hUaff hflat 0
  have := flat_X f U F hUaff hflat 1
  Stacks.TwoTermComplex.HasFiniteProjectiveModel.of_isNoetherianRing
    (moduleFinite_ker f U F hU hUaff) (moduleFinite_coker f U F hU hUaff)

omit [IsSeparated f] in
include hU hUaff in
/-- **The locus of points whose fibre has vanishing `H¹` and `r`-dimensional `H⁰` is open**,
over a Noetherian affine base. -/
theorem isOpen_setOf_fibre_cohomology [IsNoetherianRing A] [IsProper f] [F.IsCoherent]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) (r : ℕ) :
    IsOpen {p : PrimeSpectrum A |
      IsZero (cohomologyOverField p.asIdeal.ResidueField (fibreProj f p)
        ((Scheme.Modules.pullback (fibreMap f p)).obj F) 1) ∧
      Module.finrank p.asIdeal.ResidueField (cohomologyOverField p.asIdeal.ResidueField
        (fibreProj f p) ((Scheme.Modules.pullback (fibreMap f p)).obj F) 0) = r} := by
  have := flat_X f U F hUaff hflat 1
  have h := (hasFiniteProjectiveModel f U F hU hUaff
    hflat).isOpen_setOf_surjective_fibre_and_finrank_ker_eq r
  have : {p : PrimeSpectrum A |
      IsZero (cohomologyOverField p.asIdeal.ResidueField (fibreProj f p)
        ((Scheme.Modules.pullback (fibreMap f p)).obj F) 1) ∧
      Module.finrank p.asIdeal.ResidueField (cohomologyOverField p.asIdeal.ResidueField
        (fibreProj f p) ((Scheme.Modules.pullback (fibreMap f p)).obj F) 0) = r} =
      {p : PrimeSpectrum A | Function.Surjective ((cechD f U F).baseChange p.asIdeal.ResidueField) ∧
        Module.finrank p.asIdeal.ResidueField
          (LinearMap.ker ((cechD f U F).baseChange p.asIdeal.ResidueField)) = r} := by
    ext p
    simp only [Set.mem_ofPred_eq]
    rw [isZero_cohomologyOverField_one_iff f U F hU hUaff p,
      finrank_cohomologyOverField_zero_eq f U F hU hUaff p]
  rw [this]
  exact h

omit [IsSeparated f] in
include hU hUaff in
/-- **The fibre Euler characteristic is locally constant**, over a Noetherian affine base. -/
theorem isLocallyConstant_fibre_euler [IsNoetherianRing A] [IsProper f] [F.IsCoherent]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    IsLocallyConstant fun p : PrimeSpectrum A =>
      (Module.finrank p.asIdeal.ResidueField (cohomologyOverField p.asIdeal.ResidueField
          (fibreProj f p) ((Scheme.Modules.pullback (fibreMap f p)).obj F) 0) : ℤ) -
        Module.finrank p.asIdeal.ResidueField (cohomologyOverField p.asIdeal.ResidueField
          (fibreProj f p) ((Scheme.Modules.pullback (fibreMap f p)).obj F) 1) := by
  have := flat_X f U F hUaff hflat 1
  have h := (hasFiniteProjectiveModel f U F hU hUaff hflat).isLocallyConstant_fibreEuler
  have : (fun p : PrimeSpectrum A =>
      (Module.finrank p.asIdeal.ResidueField (cohomologyOverField p.asIdeal.ResidueField
          (fibreProj f p) ((Scheme.Modules.pullback (fibreMap f p)).obj F) 0) : ℤ) -
        Module.finrank p.asIdeal.ResidueField (cohomologyOverField p.asIdeal.ResidueField
          (fibreProj f p) ((Scheme.Modules.pullback (fibreMap f p)).obj F) 1)) =
      fun p => (Module.finrank p.asIdeal.ResidueField
          (LinearMap.ker ((cechD f U F).baseChange p.asIdeal.ResidueField)) : ℤ) -
        Module.finrank p.asIdeal.ResidueField
          (p.asIdeal.ResidueField ⊗[A] (Stacks.Cech.alternatingCechModuleComplex f U F).X 1 ⧸
            LinearMap.range ((cechD f U F).baseChange p.asIdeal.ResidueField)) := by
    funext p
    rw [finrank_cohomologyOverField_zero_eq f U F hU hUaff p,
      finrank_cohomologyOverField_one_eq f U F hU hUaff p]
  rw [this]
  exact h

/-! ### The canonical fibres -/

/-- A prime of `A`, read as a point of the scheme `Spec A`. -/
abbrev specPoint (p : PrimeSpectrum A) : Spec (.of A) := p

/-- The morphism `Spec κ(p) ⟶ Spec A` induced by the residue map is the identification of
`Spec κ(p)` with the spectrum of the residue field of the scheme `Spec A` at `p`, followed by the
canonical morphism from that spectrum to `Spec A`. -/
theorem specMap_residueMap (p : PrimeSpectrum A) :
    Spec.map (CommRingCat.ofHom (residueMap p)) =
      Spec.map (Scheme.Spec.residueFieldIso (.of A) (specPoint p)).hom ≫
        (Spec (.of A)).fromSpecResidueField (specPoint p) := by
  have h := Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of A) (specPoint p)
  rw [← h, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.id_comp]

omit [IsSeparated f] in
/-- The fibre over a prime, built with the residue map, computes the canonical fibre cohomology. -/
theorem finrank_fibre_eq_fibreCohomology [IsProper f] (p : PrimeSpectrum A) (n : ℕ) :
    Module.finrank p.asIdeal.ResidueField (cohomologyOverField p.asIdeal.ResidueField
        (fibreProj f p) ((Scheme.Modules.pullback (fibreMap f p)).obj F) n) =
      Module.finrank ((Spec (.of A)).residueField (specPoint p))
        (Stacks.FibreCohomology.fibreCohomology f F (specPoint p) n) := by
  have hsq := isPullback_fibre f p
  rw [specMap_residueMap] at hsq
  exact Stacks.FibreCohomology.finrank_eq_of_isPullback f F (specPoint p)
    (Scheme.Spec.residueFieldIso (.of A) (specPoint p)).hom _ _ hsq _ (Iso.refl _) n

omit [IsSeparated f] in
include hU hUaff in
/-- **The canonical fibre locus with vanishing `H¹` and `r`-dimensional `H⁰` is open**, over a
Noetherian affine base. -/
theorem isOpen_setOf_fibreCohomology [IsNoetherianRing A] [IsProper f] [F.IsCoherent]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) (r : ℕ) :
    IsOpen {x : Spec (.of A) |
      Module.finrank ((Spec (.of A)).residueField x)
          (Stacks.FibreCohomology.fibreCohomology f F x 1) = 0 ∧
        Module.finrank ((Spec (.of A)).residueField x)
          (Stacks.FibreCohomology.fibreCohomology f F x 0) = r} := by
  have := flat_X f U F hUaff hflat 1
  have hM := hasFiniteProjectiveModel f U F hU hUaff hflat
  have key : {p : PrimeSpectrum A |
      Module.finrank ((Spec (.of A)).residueField (specPoint p))
          (Stacks.FibreCohomology.fibreCohomology f F (specPoint p) 1) = 0 ∧
        Module.finrank ((Spec (.of A)).residueField (specPoint p))
          (Stacks.FibreCohomology.fibreCohomology f F (specPoint p) 0) = r} =
      {p : PrimeSpectrum A |
        IsZero (cohomologyOverField p.asIdeal.ResidueField (fibreProj f p)
          ((Scheme.Modules.pullback (fibreMap f p)).obj F) 1) ∧
        Module.finrank p.asIdeal.ResidueField (cohomologyOverField p.asIdeal.ResidueField
          (fibreProj f p) ((Scheme.Modules.pullback (fibreMap f p)).obj F) 0) = r} := by
    ext p
    simp only [Set.mem_ofPred_eq]
    rw [← finrank_fibre_eq_fibreCohomology f F p 1, ← finrank_fibre_eq_fibreCohomology f F p 0]
    refine and_congr_left fun _ => ?_
    have hfd := hM.finiteDimensional_coker_fibre p
    have : FiniteDimensional p.asIdeal.ResidueField (cohomologyOverField p.asIdeal.ResidueField
        (fibreProj f p) ((Scheme.Modules.pullback (fibreMap f p)).obj F) 1) :=
      Module.Finite.equiv (cohomologyOverFieldOneEquiv' f U F hU hUaff p).symm
    rw [ModuleCat.isZero_iff_subsingleton, Module.finrank_zero_iff]
  have h := isOpen_setOf_fibre_cohomology f U F hU hUaff hflat r
  rw [← key] at h
  exact h

omit [IsSeparated f] in
include hU hUaff in
/-- **The canonical fibre Euler characteristic is locally constant**, over a Noetherian affine
base. -/
theorem isLocallyConstant_fibreCohomology_euler [IsNoetherianRing A] [IsProper f] [F.IsCoherent]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    IsLocallyConstant fun x : Spec (.of A) =>
      (Module.finrank ((Spec (.of A)).residueField x)
          (Stacks.FibreCohomology.fibreCohomology f F x 0) : ℤ) -
        Module.finrank ((Spec (.of A)).residueField x)
          (Stacks.FibreCohomology.fibreCohomology f F x 1) := by
  have h := isLocallyConstant_fibre_euler f U F hU hUaff hflat
  have key : (fun p : PrimeSpectrum A =>
      (Module.finrank ((Spec (.of A)).residueField (specPoint p))
          (Stacks.FibreCohomology.fibreCohomology f F (specPoint p) 0) : ℤ) -
        Module.finrank ((Spec (.of A)).residueField (specPoint p))
          (Stacks.FibreCohomology.fibreCohomology f F (specPoint p) 1)) =
      fun p : PrimeSpectrum A =>
      (Module.finrank p.asIdeal.ResidueField (cohomologyOverField p.asIdeal.ResidueField
          (fibreProj f p) ((Scheme.Modules.pullback (fibreMap f p)).obj F) 0) : ℤ) -
        Module.finrank p.asIdeal.ResidueField (cohomologyOverField p.asIdeal.ResidueField
          (fibreProj f p) ((Scheme.Modules.pullback (fibreMap f p)).obj F) 1) := by
    funext p
    rw [finrank_fibre_eq_fibreCohomology f F p 0, finrank_fibre_eq_fibreCohomology f F p 1]
  rw [← key] at h
  exact h

end Stacks.TwoAffineCech
