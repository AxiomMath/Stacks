module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import StacksFrontier.Deformation.Examples.Linear.ResidueFieldBase

/-!
# Objects of the base category supported on a field

An object of `𝒞_Λ` whose carrier is a field is a terminal object: the residue map of a field
is invertible, so there is exactly one morphism into it from any object, namely the reduction
modulo the maximal ideal followed by the two chosen identifications with `k`. This file proves
that, in the form that applies both to `Deformation.Examples.residueFieldBase` and to
`Deformation.residueFieldObject`.

## Main definitions

* `Deformation.Examples.residueFieldQuotientEquiv`: the inverse of the residue map of a field,
  as a `Λ`-algebra isomorphism.
* `Deformation.Examples.toResidueFieldLike`: the morphism of `𝒞_Λ` into an object whose
  residue map is invertible.

## Main results

* `Deformation.Examples.residueFieldQuotientEquiv_residue`: the inverse of the residue map
  does invert it.
* `Deformation.Examples.isTerminal_of_residueFieldQuotientEquiv`: an object of `𝒞_Λ` whose
  residue map admits a two-sided inverse is terminal.

## Implementation notes

Terminality is stated through a supplied inverse of the residue map rather than through a
hypothesis that the carrier is a field, because the carrier of an object of `𝒞_Λ` is a
structure projection: a `Field` instance on it is not found by synthesis, and supplying one
locally creates a second `CommRing` structure on the carrier that the structure's own `Algebra`
instance does not match.

## References

* [Stacks Project, Tag 06GC](https://stacks.math.columbia.edu/tag/06GC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace Deformation.Examples

/-- The residue map of a field is an isomorphism; this is its inverse, as a `Λ`-algebra
isomorphism from the residue field of `R` to `R`. -/
noncomputable def residueFieldQuotientEquiv (Λ : Type u) (R : Type w) [CommRing Λ] [Field R]
    [Algebra Λ R] : IsLocalRing.ResidueField R ≃ₐ[Λ] R :=
  (Ideal.quotientEquivAlgOfEq Λ (IsLocalRing.maximalIdeal_eq_bot (R := R))).trans
    (AlgEquiv.quotientBot Λ R)

/-- `residueFieldQuotientEquiv Λ R` sends the residue class of `a : R` back to `a`. -/
@[simp]
theorem residueFieldQuotientEquiv_residue (Λ : Type u) {R : Type w} [CommRing Λ] [Field R]
    [Algebra Λ R] (a : R) :
    residueFieldQuotientEquiv Λ R (IsLocalRing.residue R a) = a := by
  have hmax : IsLocalRing.maximalIdeal R = ⊥ := IsLocalRing.maximalIdeal_eq_bot
  show ((Ideal.quotientEquivAlgOfEq Λ hmax).trans
    (AlgEquiv.quotientBot Λ R)) (Ideal.Quotient.mk _ a) = a
  simp only [AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk, AlgEquiv.quotientBot_mk]

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The morphism of `𝒞_Λ` from an arbitrary object to an object `T` whose residue map has the
two-sided inverse `e`: reduce modulo the maximal ideal, transport along the two chosen
identifications with `k`, and apply `e`. -/
noncomputable def toResidueFieldLike {T : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (e : IsLocalRing.ResidueField T ≃ₐ[Λ] T)
    (he : ∀ t : T, e (IsLocalRing.residue T t) = t)
    (A : ArtinianLocalAlgCat.{u, w, w} Λ k) : A ⟶ T := by
  let resAlg : A →ₐ[Λ] IsLocalRing.ResidueField A :=
    IsScalarTower.toAlgHom Λ A (IsLocalRing.ResidueField A)
  let f : A →ₐ[Λ] T :=
    e.toAlgHom.comp (T.residueEquiv.symm.toAlgHom.comp
      (A.residueEquiv.toAlgHom.comp resAlg))
  have hres (z : IsLocalRing.ResidueField T) : IsLocalRing.residue T (e z) = z :=
    e.injective (he (e z))
  refine { hom := f, isLocal := ?_, residue_comm := ?_ }
  · change IsLocalHom (e.toAlgHom.toRingHom.comp (T.residueEquiv.symm.toAlgHom.toRingHom.comp
      (A.residueEquiv.toAlgHom.toRingHom.comp (IsLocalRing.residue A))))
    infer_instance
  · intro a
    change T.residueEquiv (IsLocalRing.residue T
      (e (T.residueEquiv.symm (A.residueEquiv (IsLocalRing.residue A a))))) = _
    rw [hres, T.residueEquiv.apply_symm_apply]

/-- An object of `𝒞_Λ` whose residue map admits a two-sided inverse is a terminal object. -/
noncomputable def isTerminal_of_residueFieldQuotientEquiv
    (T : ArtinianLocalAlgCat.{u, w, w} Λ k)
    (e : IsLocalRing.ResidueField T ≃ₐ[Λ] T)
    (he : ∀ t : T, e (IsLocalRing.residue T t) = t) : IsTerminal T := by
  refine IsTerminal.ofUniqueHom (toResidueFieldLike e he) fun A f => ?_
  apply ArtinianLocalAlgCat.hom_ext
  ext a
  have hres : IsLocalRing.residue T (f.hom a) =
      IsLocalRing.residue T ((toResidueFieldLike e he A).hom a) :=
    T.residueEquiv.injective
      ((f.residue_comm a).trans ((toResidueFieldLike e he A).residue_comm a).symm)
  simpa only [he] using congrArg e hres

/-- The residue field is a terminal object of `𝒞_Λ`. -/
noncomputable def isTerminal_residueFieldBase : IsTerminal (residueFieldBase Λ k) :=
  isTerminal_of_residueFieldQuotientEquiv _ (residueFieldQuotientEquiv Λ k)
    (residueFieldQuotientEquiv_residue Λ)

end Deformation.Examples
