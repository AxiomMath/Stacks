module

public import StacksFrontier.AlgebraicGeometry.Curves.IsSplitNode
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.ResidueFields
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.SplitNode
public import StacksFrontier.AlgebraicGeometry.MinimalPrimeResidueLocalization.Stalk
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Normalization
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationBranches
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationFiber
import all StacksFrontier.AlgebraicGeometry.Curves.NodeNormalizationSeparable

/-!
# The fibre of the normalization above a split node

Let `k` be a field, let `X` be locally of finite type over `k` and let `x` be a point whose local
ring is a nodal `k`-algebra with residue field `k` and split quadratic algebra. Then the residue
field of the normalization `X^ν` at every point above `x` is again `k`.

Together with the branch count this is condition (2) of Stacks Tag 0CBW: the points of `X^ν`
above `x` are counted by the branches of `𝒪_{X,x}`
(`AlgebraicGeometry.numberOfBranches_eq_encard_normalizationFiber`, Stacks Tag 0C1S), which are
two exactly when the quadratic algebra splits (Stacks Tag 0CBU), and here each of them is shown
to have residue field `k`.

The residue-field computation is algebraic. A maximal ideal `m` of `A' = integralClosure A
(FractionRing A)` contains `𝔪_A A'`, so `A' ⧸ m` is a quotient of the quadratic algebra
`Stacks.Curves.quadraticAlgebra A = A' ⧸ 𝔪_A A'`; when that algebra is `κ × κ` the quotient
receives a surjection from `κ × κ`, and a surjection of `κ × κ` onto a ring without zero divisors
kills one of the two idempotents `(1, 0)`, `(0, 1)` and therefore restricts to a surjection on
the diagonal copy of `κ`. So the residue field at `m` is `κ`, which is `k` at a split node.

Carrying this to the fibre of the normalization morphism uses the same chain as
`Stacks.Curves.isSeparableExtension_residueField_normalization_of_isNodalAlgebra`: the points of
`X^ν` above `x` are the maximal ideals of the stalk of `ν_* 𝒪_{X^ν}`, compatibly with residue
fields (`AlgebraicGeometry.normalizationFiberEquivMaximalSpectrum`), and that stalk is `A'`
because the local ring at a node is reduced (Stacks Tag 0C3B, part (2)).

## Main results

* `Stacks.Curves.surjective_comp_algebraMap_of_nonempty_algEquiv_prod` — a surjection of a split
  quadratic algebra onto a ring without zero divisors is already surjective on the base field.
* `Stacks.Curves.bijective_algebraMap_residueField_integralClosure_of_nonempty_algEquiv_prod` —
  the residue field at a maximal ideal of the normalization of a local ring with residue field
  `k` and split quadratic algebra is `k`.
* `Stacks.Curves.bijective_fieldToResidue_normalization_of_isNodalAlgebra` — the residue field of
  the normalization above such a point is `k`.
* `Stacks.Curves.bijective_fieldToResidue_of_bijective_fieldToResidue_normalization` — the
  converse passage: if some point of the normalization above `x` has residue field `k`, so does
  `x`.

## Implementation notes

The `k`-algebra structure on the residue field of the normalization is read off the ring
homomorphism `AlgebraicGeometry.fieldToResidue` of the composite structure morphism `ν ≫ f`, the
same form in which `Stacks.Curves.IsSplitNode` records that `κ(x)` is `k`; its factorization
through `𝒪_{X,x}` is the naturality of evaluation of global sections at a point, as in
`Stacks.Curves.isSeparableExtension_residueField_normalization_of_isNodalAlgebra`.

The algebraic step is stated as the surjectivity of a composite of ring homomorphisms rather than
of an `algebraMap` out of the quotient, so that no algebra structure on the quotient enters: the
quotient of a quadratic algebra carries two competing ones, through the residue field and through
the integral closure, and the statement would have to choose.

No `@[stacks]` tag is carried here: these are components of Stacks Tag 0CBW, whose statement is
`Stacks.Curves.isSplitNode_tfae_normalizationFibre_adicCompletion`.

## References

* [Stacks Project, Tag 0CBW](https://stacks.math.columbia.edu/tag/0CBW)
* [Stacks Project, Tag 0CBU](https://stacks.math.columbia.edu/tag/0CBU)
* [Stacks Project, Tag 0CBT](https://stacks.math.columbia.edu/tag/0CBT)
* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
* [Stacks Project, Tag 0C1S](https://stacks.math.columbia.edu/tag/0C1S)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry IsLocalRing
open Stacks.NormalizationStalkAmbient

universe u v

namespace Stacks.Curves

/-! ### A surjection out of a split quadratic algebra -/

/-- **A surjection of a split quadratic algebra onto a ring without zero divisors is surjective
already on the base field.**

The images of the two idempotents `(1, 0)` and `(0, 1)` of `κ × κ` have product zero and sum one,
so one of them is zero and the other one; every element of the target is then the image of a
constant. -/
public theorem surjective_comp_algebraMap_of_nonempty_algEquiv_prod
    {κ : Type u} [Field κ] {T L : Type v} [CommRing T] [CommRing L] [Nontrivial L]
    [NoZeroDivisors L] [Algebra κ T] (hsplit : Nonempty (T ≃ₐ[κ] (κ × κ)))
    (σ : T →+* L) (hσ : Function.Surjective σ) :
    Function.Surjective (σ.comp (algebraMap κ T)) := by
  obtain ⟨φ⟩ := hsplit
  intro z
  obtain ⟨t, rfl⟩ := hσ z
  obtain ⟨⟨a, b⟩, rfl⟩ := φ.symm.surjective t
  have hprod : ((1, 0) * (0, 1) : κ × κ) = 0 := by simp [Prod.ext_iff]
  have hone : ((1, 0) + (0, 1) : κ × κ) = 1 := by simp [Prod.ext_iff]
  have hmul : σ (φ.symm (1, 0)) * σ (φ.symm (0, 1)) = 0 := by
    rw [← map_mul, ← map_mul, hprod, map_zero, map_zero]
  have hsum : σ (φ.symm (1, 0)) + σ (φ.symm (0, 1)) = 1 := by
    rw [← map_add, ← map_add, hone, map_one, map_one]
  have hdecomp : ((a, b) : κ × κ) =
      algebraMap κ (κ × κ) a * (1, 0) + algebraMap κ (κ × κ) b * (0, 1) := by
    simp
  have hval : σ (φ.symm (a, b)) = σ (algebraMap κ T a) * σ (φ.symm (1, 0)) +
      σ (algebraMap κ T b) * σ (φ.symm (0, 1)) := by
    rw [hdecomp]
    simp only [map_add, map_mul, φ.symm.commutes]
  simp only [RingHom.comp_apply]
  rcases mul_eq_zero.mp hmul with h | h
  · rw [h, zero_add] at hsum
    exact ⟨b, by rw [hval, h, hsum]; ring⟩
  · rw [h, add_zero] at hsum
    exact ⟨a, by rw [hval, h, hsum]; ring⟩

/-! ### The residue fields of the normalization of a split node -/

/-- **The residue field at a maximal ideal of the normalization of a local ring with split
quadratic algebra is the residue field of the ring.**

A maximal ideal `m` of `A' = integralClosure A (FractionRing A)` contains `𝔪_A A'`
(`Stacks.Curves.map_maximalIdeal_le_of_isMaximal`), so the third isomorphism theorem presents
`A' ⧸ m` as a quotient of `quadraticAlgebra A`; if the latter is `κ × κ` then the composite
`κ → quadraticAlgebra A → A' ⧸ m` is surjective, and `A' ⧸ m` is the residue field at `m`. -/
public theorem bijective_algebraMap_residueField_integralClosure_of_nonempty_algEquiv_prod
    (k : Type u) (A : Type u) [Field k] [CommRing A] [IsLocalRing A] [Algebra k A]
    (hres : Function.Bijective (algebraMap k (ResidueField A)))
    (hsplit : Nonempty (quadraticAlgebra A ≃ₐ[ResidueField A]
      (ResidueField A × ResidueField A)))
    (m : MaximalSpectrum ↥(integralClosure A (FractionRing A))) :
    Function.Bijective (algebraMap k m.asIdeal.ResidueField) := by
  have hm : m.asIdeal.IsMaximal := m.isMaximal
  have hJm : (maximalIdeal A).map
      (algebraMap A ↥(integralClosure A (FractionRing A))) ≤ m.asIdeal :=
    map_maximalIdeal_le_of_isMaximal m.asIdeal
  -- the third isomorphism theorem, and the residue field as the quotient
  let e := DoubleQuot.quotQuotEquivQuotOfLEₐ k
    (A := ↥(integralClosure A (FractionRing A)))
    (I := (maximalIdeal A).map (algebraMap A ↥(integralClosure A (FractionRing A))))
    (J := m.asIdeal) hJm
  let eRes : (↥(integralClosure A (FractionRing A)) ⧸ m.asIdeal) ≃ₐ[k] m.asIdeal.ResidueField :=
    residueFieldAlgEquivQuotient k m.asIdeal
  let etot := e.trans eRes
  let Ibar : Ideal (quadraticAlgebra A) :=
    m.asIdeal.map (Ideal.Quotient.mkₐ k
      ((maximalIdeal A).map (algebraMap A ↥(integralClosure A (FractionRing A)))))
  -- the surjection of the quadratic algebra onto the residue field at `m`
  let σ : quadraticAlgebra A →+* m.asIdeal.ResidueField :=
    etot.toRingEquiv.toRingHom.comp (Ideal.Quotient.mk Ibar)
  have hσ : Function.Surjective σ :=
    (EquivLike.surjective etot).comp Ideal.Quotient.mk_surjective
  have hρ : Function.Surjective (σ.comp (algebraMap (ResidueField A) (quadraticAlgebra A))) :=
    surjective_comp_algebraMap_of_nonempty_algEquiv_prod hsplit σ hσ
  -- the base field reaches the residue field at `m` through the residue field of `A`
  have hcomm : (σ.comp (algebraMap (ResidueField A) (quadraticAlgebra A))).comp
      (algebraMap k (ResidueField A)) = algebraMap k m.asIdeal.ResidueField := by
    refine RingHom.ext fun c ↦ ?_
    change σ (algebraMap (ResidueField A) (quadraticAlgebra A)
      (algebraMap k (ResidueField A) c)) = _
    rw [← IsScalarTower.algebraMap_apply k (ResidueField A) (quadraticAlgebra A) c]
    change etot (Ideal.Quotient.mk Ibar (algebraMap k (quadraticAlgebra A) c)) = _
    rw [← Ideal.Quotient.mk_algebraMap (R₁ := k)]
    exact etot.commutes c
  refine ⟨(algebraMap k m.asIdeal.ResidueField).injective, ?_⟩
  rw [← hcomm]
  exact hρ.comp hres.2

/-! ### The residue fields of the fibre of the normalization -/

/-- The map from the base field to the residue field of the normalization at a point above `x`
factors through the local ring of `X` at `x`. -/
private theorem fieldToResidue_normalization_apply
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ AlgebraicGeometry.Spec (.of k))
    [LocallyOfFiniteType f] (x' : normalizationSchemeOverField k f) (c : k) :
    (fieldToResidue (normalizationOverField k f ≫ f) x').hom c =
      ((normalizationOverField k f).residueFieldMap x').hom
        ((X.residue (normalizationOverField k f x')).hom
          ((fieldToStalk f (normalizationOverField k f x')).hom c)) := by
  change ((normalizationSchemeOverField k f).Γevaluation x').hom
    ((Scheme.Hom.appTop (normalizationOverField k f ≫ f)).hom
      ((Scheme.ΓSpecIso (.of k)).inv.hom c)) = _
  rw [show Scheme.Hom.appTop (normalizationOverField k f ≫ f) =
    f.appTop ≫ (normalizationOverField k f).appTop by simp]
  exact (Scheme.Γevaluation_naturality_apply (normalizationOverField k f) x'
    (f.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom c))).symm

/-- **The residue field of the normalization above a split node is the base field.**

Let `x` be a point whose local ring is a nodal `k`-algebra with residue field `k` and split
quadratic algebra. Then every point of the normalization above `x` has residue field `k`. -/
public theorem bijective_fieldToResidue_normalization_of_isNodalAlgebra
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ AlgebraicGeometry.Spec (.of k))
    [LocallyOfFiniteType f] (x : X)
    (hnodal :
      letI : Algebra k (X.presheaf.stalk x) := (fieldToStalk f x).hom.toAlgebra
      IsNodalAlgebra k (X.presheaf.stalk x))
    (hres : Function.Bijective (fieldToResidue f x).hom)
    (hsplit : Nonempty (quadraticAlgebra (X.presheaf.stalk x) ≃ₐ[ResidueField (X.presheaf.stalk x)]
      (ResidueField (X.presheaf.stalk x) × ResidueField (X.presheaf.stalk x)))) :
    ∀ x' : normalizationSchemeOverField k f, normalizationOverField k f x' = x →
      Function.Bijective (fieldToResidue (normalizationOverField k f ≫ f) x').hom := by
  intro x' hx'
  subst hx'
  set hX := finite_irreducibleComponents_of_locallyOfFiniteType k f
  set ν := normalizationOverField k f
  set x := ν x'
  let : Algebra k (X.presheaf.stalk x) := (fieldToStalk f x).hom.toAlgebra
  let : Algebra k (X.residueField x) := (fieldToResidue f x).hom.toAlgebra
  have hred : IsReduced (X.presheaf.stalk x) := hnodal.2.1
  let : IsReduced (X.presheaf.stalk x) := hred
  -- the pushforward stalk of the normalization, and its description as the integral closure
  let : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
    normalizationPushforwardStalkAlgebra X hX x
  let : Algebra (X.presheaf.stalk x)
      (FractionRing (X.presheaf.stalk x ⧸ nilradical (X.presheaf.stalk x))) :=
    (reductionFractionRingHom (X.presheaf.stalk x)).toAlgebra
  let eS : normalizationPushforwardStalk X hX x ≃ₐ[X.presheaf.stalk x]
      ↥(integralClosure (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x))) :=
    (normalizationStalkAlgEquivIntegralClosureFractionRing X hX x).trans
      (fractionRingReductionAlgEquiv (X.presheaf.stalk x) hred).mapIntegralClosure
  obtain ⟨fiberEquiv, fiberResidue⟩ := normalizationFiberEquivMaximalSpectrum X hX x
  let y : {z : Scheme.normalizationScheme X hX // Scheme.normalization X hX z = x} := ⟨x', rfl⟩
  obtain ⟨e, -, he2⟩ := fiberResidue y
  -- the matching maximal ideal of the integral closure
  let m : MaximalSpectrum
      ↥(integralClosure (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x))) :=
    MaximalSpectrum.congr eS.toRingEquiv (fiberEquiv y)
  have : (m.asIdeal).IsMaximal := m.isMaximal
  let eQuot : (normalizationPushforwardStalk X hX x ⧸ (fiberEquiv y).asIdeal) ≃ₐ[X.presheaf.stalk x]
      (↥(integralClosure (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x))) ⧸ m.asIdeal) :=
    Ideal.quotientEquivAlg (fiberEquiv y).asIdeal m.asIdeal eS rfl
  let eRes : (↥(integralClosure (X.presheaf.stalk x)
        (FractionRing (X.presheaf.stalk x))) ⧸ m.asIdeal) ≃ₐ[k] m.asIdeal.ResidueField :=
    residueFieldAlgEquivQuotient k m.asIdeal
  have hmres : Function.Bijective (algebraMap k m.asIdeal.ResidueField) :=
    bijective_algebraMap_residueField_integralClosure_of_nonempty_algEquiv_prod k
      (X.presheaf.stalk x) hres hsplit m
  -- the composite ring equivalence, and its compatibility with `k`
  let ψ : (normalizationSchemeOverField k f).residueField x' ≃+* m.asIdeal.ResidueField :=
    (e.trans eQuot.toRingEquiv).trans eRes.toRingEquiv
  have hcommA : ∀ a : X.presheaf.stalk x,
      ψ ((ν.residueFieldMap x').hom ((X.residue x).hom a)) =
        algebraMap (X.presheaf.stalk x) m.asIdeal.ResidueField a := by
    intro a
    have h2 := congrArg (fun g : X.presheaf.stalk x →+* _ => g a) he2
    simp only [RingHom.comp_apply] at h2
    rw [show (Scheme.residueFieldCongr (y.property.symm)).hom.hom ((X.residue x).hom a) =
      (X.residue x).hom a by simp] at h2
    simp only [ψ, RingEquiv.trans_apply]
    rw [show e ((ν.residueFieldMap x').hom ((X.residue x).hom a)) =
      Ideal.Quotient.mk (fiberEquiv y).asIdeal
        (algebraMap (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) a) from h2,
      show eQuot.toRingEquiv (Ideal.Quotient.mk (fiberEquiv y).asIdeal
          (algebraMap (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) a)) =
        Ideal.Quotient.mk m.asIdeal (algebraMap (X.presheaf.stalk x)
          ↥(integralClosure (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x))) a) by
        simp [eQuot]]
    exact (IsScalarTower.algebraMap_apply (X.presheaf.stalk x)
      (↥(integralClosure (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x))) ⧸ m.asIdeal)
      m.asIdeal.ResidueField a).symm
  have hcommk : ∀ c : k, ψ ((fieldToResidue (ν ≫ f) x').hom c) =
      algebraMap k m.asIdeal.ResidueField c := by
    intro c
    rw [fieldToResidue_normalization_apply k f x' c, hcommA ((fieldToStalk f x).hom c)]
    rfl
  have hfun : ((ψ : _ →+* m.asIdeal.ResidueField).comp
      (fieldToResidue (ν ≫ f) x').hom : k → _) = algebraMap k m.asIdeal.ResidueField :=
    funext hcommk
  refine (Function.Bijective.of_comp_iff' (EquivLike.bijective ψ) _).mp ?_
  change Function.Bijective (((ψ : _ →+* m.asIdeal.ResidueField).comp
    (fieldToResidue (ν ≫ f) x').hom : k → _))
  rw [hfun]
  exact hmres

/-- **The residue field of a point is the base field as soon as the residue field of one point of
the normalization above it is.** The residue field of `X` at `x` sits inside the residue field of
the normalization at a point above `x`, so a surjection of `k` onto the latter forces one onto the
former. -/
public theorem bijective_fieldToResidue_of_bijective_fieldToResidue_normalization
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ AlgebraicGeometry.Spec (.of k))
    [LocallyOfFiniteType f] (x : X) (x' : normalizationSchemeOverField k f)
    (hx' : normalizationOverField k f x' = x)
    (hres : Function.Bijective (fieldToResidue (normalizationOverField k f ≫ f) x').hom) :
    Function.Bijective (fieldToResidue f x).hom := by
  subst hx'
  refine ⟨(fieldToResidue f (normalizationOverField k f x')).hom.injective, fun α ↦ ?_⟩
  obtain ⟨c, hc⟩ := hres.2 (((normalizationOverField k f).residueFieldMap x').hom α)
  refine ⟨c, ((normalizationOverField k f).residueFieldMap x').hom.injective ?_⟩
  rw [← hc, fieldToResidue_normalization_apply k f x' c]
  rfl

end Stacks.Curves

end
