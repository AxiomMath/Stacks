module

public import StacksFrontier.AlgebraicGeometry.Descent.FpqcAffine
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.AffineTarget
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Field
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Module
public import StacksFrontier.RingTheory.Module.LocallyFree.Field
public import Mathlib.RingTheory.Finiteness.Descent

/-!
# Finite locally free morphisms to the spectrum of a field

A morphism to the spectrum of a field is finite locally free of rank `d` exactly when it is affine
and the global sections of its source form a `d`-dimensional vector space. In particular the rank
of such a morphism is detected after any extension of the base field, which makes it descend along
the spectrum of an extension of fields.

## Main results

* `Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_module_of_specTarget` identifies, for a morphism
  to the spectrum of a ring, finite local freeness of a given rank with the module-level condition
  on the global sections of the source.
* `Stacks.Morphisms.specSectionsAlgEquiv` identifies the global sections of the spectrum of an
  algebra with that algebra.
* `Stacks.Morphisms.isFiniteLocallyFreeOfRank_specMap_iff_module` is the module-level condition for
  the morphism of spectra induced by an algebra.
* `Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_finrank_of_specTarget` is the same statement over
  a field, where the module-level condition is finite dimensionality of the given dimension.
* `Stacks.Morphisms.isFiniteLocallyFreeOfRank_of_isPullback_of_field` descends the rank along an
  extension of fields.

## Implementation notes

The algebra structure on the global sections of the source is taken as an argument together with
the equation identifying its structure map, as in
`Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_module_of_isAffine`. Over the spectrum of a ring
that structure map is the action on global sections composed with
`AlgebraicGeometry.Scheme.ΓSpecIso`, not the action on global sections alone.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TensorProduct

universe u

namespace Stacks.Morphisms

/-- For a morphism to the spectrum of a ring, being finite locally free of rank `d` is the
module-level condition on the global sections of the source. -/
theorem isFiniteLocallyFreeOfRank_iff_module_of_specTarget {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) [IsAffineHom f] (d : ℕ) [alg : Algebra ↑R ↑Γ(X, ⊤)]
    (halg : algebraMap ↑R ↑Γ(X, ⊤) = ((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom) :
    IsFiniteLocallyFreeOfRank f d ↔ Module.IsFiniteLocallyFreeOfRank ↑R ↑Γ(X, ⊤) d := by
  have halg' : alg = ((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom.toAlgebra :=
    Algebra.algebra_ext _ _ (DFunLike.congr_fun halg)
  subst halg'
  rw [isFiniteLocallyFreeOfRank_iff, and_iff_right (inferInstance : IsAffineHom f)]
  exact sheafOfModules_isFiniteLocallyFreeOfRank_iff_module f d

/-- The global sections of the spectrum of an algebra `A` over a ring `R` form an `R`-algebra
isomorphic to `A`, for the algebra structure induced by the morphism `Spec A ⟶ Spec R`. -/
noncomputable def specSectionsAlgEquiv (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    letI := ((Scheme.ΓSpecIso (.of R)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap R A))).appTop).hom.toAlgebra
    ↑Γ(Spec (.of A), ⊤) ≃ₐ[R] A :=
  let p : Spec (.of A) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let _ : Algebra R ↑Γ(Spec (.of A), ⊤) :=
    ((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop).hom.toAlgebra
  let eR : ↑Γ(Spec (.of R), ⊤) ≃+* R := (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
  let eA : ↑Γ(Spec (.of A), ⊤) ≃+* A := (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv
  have hcomp : (algebraMap R A).comp eR.toRingHom = eA.toRingHom.comp p.appTop.hom :=
    congrArg CommRingCat.Hom.hom
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R A))).symm
  { __ := eA
    commutes' x := by
      change eA (p.appTop.hom (eR.symm x)) = algebraMap R A x
      have hx := congrArg (fun φ : ↑Γ(Spec (.of R), ⊤) →+* A ↦ φ (eR.symm x)) hcomp
      simpa [RingHom.comp_apply] using hx.symm }

/-- For the morphism of spectra induced by an algebra, being finite locally free of rank `d` is
the module-level condition on that algebra. -/
theorem isFiniteLocallyFreeOfRank_specMap_iff_module (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (d : ℕ) :
    IsFiniteLocallyFreeOfRank (Spec.map (CommRingCat.ofHom (algebraMap R A))) d ↔
      Module.IsFiniteLocallyFreeOfRank R A d := by
  let p : Spec (.of A) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let _ : Algebra R ↑Γ(Spec (.of A), ⊤) :=
    ((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop).hom.toAlgebra
  rw [isFiniteLocallyFreeOfRank_iff_module_of_specTarget p d rfl]
  exact ⟨fun h ↦ Module.IsFiniteLocallyFreeOfRank.of_linearEquiv
      (specSectionsAlgEquiv R A).toLinearEquiv h,
    fun h ↦ Module.IsFiniteLocallyFreeOfRank.of_linearEquiv
      (specSectionsAlgEquiv R A).symm.toLinearEquiv h⟩

/-- A morphism to the spectrum of a field is finite locally free of rank `d` exactly when the
global sections of its source form a `d`-dimensional vector space. -/
theorem isFiniteLocallyFreeOfRank_iff_finrank_of_specTarget {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsAffineHom f] (d : ℕ) [Algebra K ↑Γ(X, ⊤)]
    (halg : algebraMap K ↑Γ(X, ⊤) = ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom) :
    IsFiniteLocallyFreeOfRank f d ↔
      (Module.Finite K ↑Γ(X, ⊤) ∧ Module.finrank K ↑Γ(X, ⊤) = d) :=
  (isFiniteLocallyFreeOfRank_iff_module_of_specTarget f d halg).trans
    (Module.isFiniteLocallyFreeOfRank_iff_finrank_eq _ d)

/-- **Descent of the rank along an extension of fields.** Let `K ⊆ L` be an extension of fields
and let `p : Z ⟶ Spec K` be a morphism of schemes whose base change `p' : Z' ⟶ Spec L` is finite
locally free of rank `r`. Then `p` itself is finite locally free of rank `r`. -/
theorem isFiniteLocallyFreeOfRank_of_isPullback_of_field {K L : Type u} [Field K] [Field L]
    [Algebra K L] {Z Z' : Scheme.{u}} {p : Z ⟶ Spec (.of K)} {p' : Z' ⟶ Spec (.of L)}
    {q : Z' ⟶ Z} (sq : IsPullback q p' p (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    (r : ℕ) (h : IsFiniteLocallyFreeOfRank p' r) : IsFiniteLocallyFreeOfRank p r := by
  set φ : CommRingCat.of K ⟶ CommRingCat.of L := CommRingCat.ofHom (algebraMap K L)
  obtain ⟨_, _⟩ := (flat_and_surjective_SpecMap_iff φ).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  have : IsAffineHom p' := h.toIsAffineHom
  have : IsAffine Z' := isAffine_of_isAffineHom p'
  have : IsAffine Z := Stacks.Descent.isAffine_of_isPullback_of_flat sq inferInstance
  let : Algebra K ↑Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom.toAlgebra
  let : Algebra L ↑Γ(Z', ⊤) := ((Scheme.ΓSpecIso (.of L)).inv ≫ p'.appTop).hom.toAlgebra
  let : Algebra ↑Γ(Z, ⊤) ↑Γ(Z', ⊤) := q.appTop.hom.toAlgebra
  let : Algebra K ↑Γ(Z', ⊤) :=
    (q.appTop.hom.comp ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom).toAlgebra
  have hsqA : IsPushout φ (Scheme.ΓSpecIso (.of K)).inv (Scheme.ΓSpecIso (.of L)).inv
      (Spec.map φ).appTop :=
    IsPushout.of_vert_isIso ⟨Scheme.ΓSpecIso_inv_naturality φ⟩
  have hpush := hsqA.paste_vert (isPushout_appTop_of_isPullback sq).flip
  have : IsScalarTower K ↑Γ(Z, ⊤) ↑Γ(Z', ⊤) := .of_algebraMap_eq' rfl
  have : IsScalarTower K L ↑Γ(Z', ⊤) := .of_algebraMap_eq' congr($(hpush.1.1).hom).symm
  have hpush' : IsPushout (CommRingCat.ofHom (algebraMap K L))
      (CommRingCat.ofHom (algebraMap K ↑Γ(Z, ⊤)))
      (CommRingCat.ofHom (algebraMap L ↑Γ(Z', ⊤)))
      (CommRingCat.ofHom (algebraMap (↑Γ(Z, ⊤)) ↑Γ(Z', ⊤))) := hpush
  have : Algebra.IsPushout K L ↑Γ(Z, ⊤) ↑Γ(Z', ⊤) :=
    CommRingCat.isPushout_iff_isPushout.mp hpush'
  obtain ⟨hfin', hrank'⟩ := (isFiniteLocallyFreeOfRank_iff_finrank_of_specTarget p' r rfl).mp h
  have he : (L ⊗[K] ↑Γ(Z, ⊤)) ≃ₗ[L] ↑Γ(Z', ⊤) :=
    (Algebra.IsPushout.equiv K L ↑Γ(Z, ⊤) ↑Γ(Z', ⊤)).toLinearEquiv
  have : Module.Finite L (L ⊗[K] ↑Γ(Z, ⊤)) := Module.Finite.equiv he.symm
  have : Module.Finite K ↑Γ(Z, ⊤) := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat L
  refine (isFiniteLocallyFreeOfRank_iff_finrank_of_specTarget p r rfl).mpr ⟨inferInstance, ?_⟩
  rwa [← Module.finrank_baseChange (R := L) (S := K) (M' := ↑Γ(Z, ⊤)), he.finrank_eq]

end Stacks.Morphisms

end
