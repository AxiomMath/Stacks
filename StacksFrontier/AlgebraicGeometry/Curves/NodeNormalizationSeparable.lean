module

public import StacksFrontier.AlgebraicGeometry.Curves.NodalAlgebra
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.ResidueFields
public import StacksFrontier.AlgebraicGeometry.Curves.NodeStalkCharacterization
public import StacksFrontier.AlgebraicGeometry.MinimalPrimeResidueLocalization.Stalk
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Normalization
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationFiber

/-!
# The residue fields of the normalization above a nodal point are separable

Let `k` be a field, let `X` be locally of finite type over `k` and let `x` be a point whose
local ring is a nodal `k`-algebra.  Then the residue field of the normalization of `X` at every
point above `x` is separable over `k`.

This is the hypothesis that Stacks Tag 0C3P and Stacks Tag 0C3Y take as input, supplied from
the nodal condition.  The algebraic statement is Stacks Tag 0C4A, available as
`Stacks.Curves.isSeparableExtension_residueField_integralClosure_fractionRing`, which speaks of
the maximal ideals of `A' = integralClosure A (FractionRing A)` for `A = 𝒪_{X,x}`; what is done
here is to carry it across to the geometric fibre of the normalization morphism.

## Main results

* `Stacks.Curves.isSeparableExtension_residueField_normalization_of_isNodalAlgebra` — the
  residue fields of the normalization above a nodal point are separable over the base field.

## Implementation notes

The chain of identifications is: the points of the normalization above `x` are the maximal
ideals of the stalk `S` of the pushforward `ν_* 𝒪_{X^ν}`, compatibly with residue fields
(`AlgebraicGeometry.normalizationFiberEquivMaximalSpectrum`); `S` is the integral closure of
`A` in the total ring of fractions of its reduction (Stacks Tag 0C3B, part (2)); and since the
local ring at a nodal point is reduced that total ring of fractions is the total ring of
fractions of `A` itself, so `S` is `A'`.

The `k`-algebra structure on the residue field of the normalization is the one Tags 0C3P and
0C3Y use, induced by the germ at the point of the structure morphism `ν ≫ f`; it is compared
with the structure induced through `𝒪_{X,x}` by the naturality of evaluation of global sections
at a point, `AlgebraicGeometry.Scheme.Γevaluation_naturality_apply`.

## References

* [Stacks Project, Tag 0C4A](https://stacks.math.columbia.edu/tag/0C4A)
* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
* [Stacks Project, Tag 0C3P](https://stacks.math.columbia.edu/tag/0C3P)
* [Stacks Project, Tag 0C3Y](https://stacks.math.columbia.edu/tag/0C3Y)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry IsLocalRing
open Stacks.NormalizationStalkAmbient

universe u v

namespace Stacks.Curves

-- `fractionRingReductionAlgEquiv` was proved privately here and, with the same statement and
-- the same proof under the name `reducedFractionRingEquiv`, in
-- `StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.NormalizationFibre`.  The one
-- canonical copy is now public in `Stacks.NormalizationStalkAmbient`, in the module that
-- declares `reductionFractionRingHom`, which this file already opens.

/-- **The residue field of the normalization at a point above a nodal point is separable over
the base field.**

This is the input that Stacks Tags 0C3P and 0C3Y require, supplied from the nodal condition on
the local ring by Stacks Tag 0C4A. -/
theorem isSeparableExtension_residueField_normalization_of_isNodalAlgebra
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ AlgebraicGeometry.Spec (.of k))
    [LocallyOfFiniteType f] (x : X)
    (hnodal :
      letI : Algebra k (X.presheaf.stalk x) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
          X.presheaf.germ ⊤ x trivial).hom.toAlgebra
      IsNodalAlgebra k (X.presheaf.stalk x)) :
    let Xnorm := normalizationSchemeOverField k f
    let ν := normalizationOverField k f
    ∀ x' : Xnorm, ν x' = x →
      letI : Algebra k (Xnorm.residueField x') :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (ν ≫ f).appTop ≫
          Xnorm.Γevaluation x').hom.toAlgebra
      Algebra.IsSeparableExtension k (Xnorm.residueField x') := by
  intro Xnorm ν x' hx'
  subst hx'
  set hX := finite_irreducibleComponents_of_locallyOfFiniteType k f
  set x := ν.base x'
  set A := X.presheaf.stalk x
  let : Algebra k A :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom.toAlgebra
  let : Algebra k (Xnorm.residueField x') :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (ν ≫ f).appTop ≫ Xnorm.Γevaluation x').hom.toAlgebra
  have hred : IsReduced A := hnodal.2.1
  have hNag : IsNagataRing A := isNagataRing_stalk_of_locallyOfFiniteType k f x
  -- the pushforward stalk of the normalization, and its description as the integral closure
  let : Algebra A (normalizationPushforwardStalk X hX x) :=
    normalizationPushforwardStalkAlgebra X hX x
  let : Algebra A (FractionRing (A ⧸ nilradical A)) := (reductionFractionRingHom A).toAlgebra
  let eS : normalizationPushforwardStalk X hX x ≃ₐ[A]
      ↥(integralClosure A (FractionRing A)) :=
    (normalizationStalkAlgEquivIntegralClosureFractionRing X hX x).trans
      (fractionRingReductionAlgEquiv A hred).mapIntegralClosure
  obtain ⟨fiberEquiv, fiberResidue⟩ := normalizationFiberEquivMaximalSpectrum X hX x
  let y : {z : Scheme.normalizationScheme X hX // Scheme.normalization X hX z = x} := ⟨x', rfl⟩
  obtain ⟨e, -, he2⟩ := fiberResidue y
  -- the matching maximal ideal of the integral closure
  let m : MaximalSpectrum ↥(integralClosure A (FractionRing A)) :=
    MaximalSpectrum.congr eS.toRingEquiv (fiberEquiv y)
  have : (m.asIdeal).IsMaximal := m.isMaximal
  -- `S ⧸ 𝔫` and `A' ⧸ m` agree as `A`-algebras
  let eQuot : (normalizationPushforwardStalk X hX x ⧸ (fiberEquiv y).asIdeal) ≃ₐ[A]
      (↥(integralClosure A (FractionRing A)) ⧸ m.asIdeal) :=
    Ideal.quotientEquivAlg (fiberEquiv y).asIdeal m.asIdeal eS rfl
  -- transport to the residue field of the maximal ideal
  let eRes : (↥(integralClosure A (FractionRing A)) ⧸ m.asIdeal) ≃ₐ[k] m.asIdeal.ResidueField :=
    residueFieldAlgEquivQuotient k m.asIdeal
  have hsep : Algebra.IsSeparableExtension k m.asIdeal.ResidueField :=
    isSeparableExtension_residueField_integralClosure_fractionRing k A hNag hnodal m
  -- the composite ring equivalence, and its compatibility with `k`
  let ψ : Xnorm.residueField x' ≃+* m.asIdeal.ResidueField :=
    (e.trans eQuot.toRingEquiv).trans eRes.toRingEquiv
  -- the composite `k → κ(x')` factors through `𝒪_{X,x}`
  have hstep : ∀ c : k, algebraMap k (Xnorm.residueField x') c =
      (ν.residueFieldMap x').hom ((X.residue x).hom (algebraMap k A c)) := by
    intro c
    show (Xnorm.Γevaluation x').hom ((Scheme.Hom.appTop (ν ≫ f)).hom
      ((Scheme.ΓSpecIso (.of k)).inv.hom c)) = _
    rw [show Scheme.Hom.appTop (ν ≫ f) = f.appTop ≫ ν.appTop by simp]
    exact (Scheme.Γevaluation_naturality_apply ν x'
      (f.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom c))).symm
  -- the comparison of the two descriptions of `κ(x')` is compatible with `𝒪_{X,x}`
  have hcommA : ∀ a : A, ψ ((ν.residueFieldMap x').hom ((X.residue x).hom a)) =
      algebraMap A m.asIdeal.ResidueField a := by
    intro a
    have h2 := congrArg (fun g : A →+* _ => g a) he2
    simp only [RingHom.comp_apply] at h2
    rw [show (Scheme.residueFieldCongr (y.property.symm)).hom.hom ((X.residue x).hom a) =
      (X.residue x).hom a by simp] at h2
    simp only [ψ, RingEquiv.trans_apply]
    rw [show e ((ν.residueFieldMap x').hom ((X.residue x).hom a)) =
      Ideal.Quotient.mk (fiberEquiv y).asIdeal
        (algebraMap A (normalizationPushforwardStalk X hX x) a) from h2,
      show eQuot.toRingEquiv (Ideal.Quotient.mk (fiberEquiv y).asIdeal
          (algebraMap A (normalizationPushforwardStalk X hX x) a)) =
        Ideal.Quotient.mk m.asIdeal (algebraMap A ↥(integralClosure A (FractionRing A)) a) from by
        simp [eQuot]]
    exact (IsScalarTower.algebraMap_apply A
      (↥(integralClosure A (FractionRing A)) ⧸ m.asIdeal) m.asIdeal.ResidueField a).symm
  -- hence it is compatible with `k`
  have hcommk : ∀ c : k, ψ (algebraMap k (Xnorm.residueField x') c) =
      algebraMap k m.asIdeal.ResidueField c := by
    intro c
    rw [hstep c, hcommA (algebraMap k A c)]
    rfl
  exact Algebra.IsSeparableExtension.of_algEquiv (AlgEquiv.ofRingEquiv (f := ψ) hcommk).symm

end Stacks.Curves

end
