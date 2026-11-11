module

public import StacksFrontier.AlgebraicGeometry.Curves.SplitNodeNormalizationFibre
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian

/-!
# Split nodes on a locally Noetherian scheme

Let `k` be a field, `X` a locally Noetherian `k`-scheme and `x ∈ X` a point whose local ring
`A = 𝒪_{X,x}` is a nodal `k`-algebra. The closing assertion of Stacks Tag 0CBU says that the
equivalent conditions of a split node (`Stacks.Curves.isSplitNode_tfae`) mean exactly that the
normalization `ν : X^ν → X` has two points `x₁, x₂` above `x`, with `κ(x) = κ(x₁) = κ(x₂)`.

The count is the branch count: the points of `X^ν` above `x` are the branches of `A`
(`AlgebraicGeometry.numberOfBranches_eq_encard_normalizationFiber`, Stacks Tag 0C1S), two exactly
when the quadratic algebra splits. For the residue fields, the points above `x` correspond to the
maximal ideals of the integral closure `A'` of `A` in its total ring of fractions, compatibly with
residue fields (`AlgebraicGeometry.normalizationFiberEquivMaximalSpectrum`, Stacks Tag 0C3B), and
the residue field of `A'` at a maximal ideal is a quotient of the quadratic algebra `A' ⧸ 𝔪_A A'`;
when the latter is `κ × κ`, it is `κ`
(`Stacks.Curves.surjective_algebraMap_residueField_integralClosure_of_nonempty_algEquiv_prod`).

Unlike `Stacks.Curves.isSplitNode_tfae_normalizationFibre_adicCompletion` (Stacks Tag 0CBW), the
residue field `κ(x)` is not assumed to be `k` and `X` need not be of finite type over `k`.

## Main results

* `Stacks.Curves.bijective_residueFieldMap_normalization_of_nonempty_algEquiv_prod` — above a
  point with reduced local ring and split quadratic algebra, the normalization has residue fields
  `κ(x)`.
* `Stacks.Curves.nonempty_quadraticAlgebra_algEquiv_prod_iff_normalizationFiber` — on a locally
  Noetherian `k`-scheme, a node is split exactly when its normalization fibre has two points,
  each with residue field `κ(x)`.

## References

* [Stacks Project, Tag 0CBU](https://stacks.math.columbia.edu/tag/0CBU)
* [Stacks Project, Tag 0C1S](https://stacks.math.columbia.edu/tag/0C1S)
* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry IsLocalRing
open Stacks.NormalizationStalkAmbient

universe u

namespace Stacks.Curves

/-! ### The split-node conditions on a locally Noetherian scheme -/

/-- **Above a split node the normalization has residue fields `κ(x)`.** Let `X` be a scheme
whose quasi-compact opens have finitely many irreducible components (for instance a locally
Noetherian scheme), and `x ∈ X` a point whose local ring is reduced with split quadratic
algebra. Then every point `x'` of the normalization above `x` has `κ(x') = κ(x)`. -/
public theorem bijective_residueFieldMap_normalization_of_nonempty_algEquiv_prod
    {X : Scheme.{u}}
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X)
    (hred : IsReduced (X.presheaf.stalk x))
    (hsplit : Nonempty (quadraticAlgebra (X.presheaf.stalk x) ≃ₐ[ResidueField (X.presheaf.stalk x)]
      (ResidueField (X.presheaf.stalk x) × ResidueField (X.presheaf.stalk x))))
    (x' : X.normalizationScheme hX) (hx' : X.normalization hX x' = x) :
    Function.Bijective ((X.normalization hX).residueFieldMap x').hom := by
  revert hred hsplit
  subst hx'
  set ν := X.normalization hX
  set x := ν x'
  intro hred hsplit
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
        (FractionRing (X.presheaf.stalk x))) ⧸ m.asIdeal) ≃ₐ[X.presheaf.stalk x]
        m.asIdeal.ResidueField :=
    residueFieldAlgEquivQuotient (X.presheaf.stalk x) m.asIdeal
  have hmres : Function.Surjective (algebraMap (X.presheaf.stalk x) m.asIdeal.ResidueField) :=
    surjective_algebraMap_residueField_integralClosure_of_nonempty_algEquiv_prod
      (X.presheaf.stalk x) hsplit m
  -- the composite ring equivalence, and its compatibility with `𝒪_{X,x}`
  let ψ : (X.normalizationScheme hX).residueField x' ≃+* m.asIdeal.ResidueField :=
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
  refine ⟨(ν.residueFieldMap x').hom.injective, fun t ↦ ?_⟩
  obtain ⟨a, ha⟩ := hmres (ψ t)
  exact ⟨(X.residue x).hom a, ψ.injective ((hcommA a).trans ha)⟩

/-- **A node is split exactly when the normalization has two points above it, each with the
same residue field.** Let `k` be a field, `X` a locally Noetherian `k`-scheme and `x ∈ X` a point
whose local ring `A = 𝒪_{X,x}` is a nodal `k`-algebra. Then the equivalent conditions of
`Stacks.Curves.isSplitNode_tfae` (and
`Stacks.Curves.nonempty_algEquiv_adicCompletion_quotient_X_mul_X_iff_numberOfBranches_eq_two`),
represented here by the splitting `κ' ≅ κ × κ` of the quadratic algebra, hold if and only if
there are exactly two points `x₁, x₂` of the normalization `X^ν` above `x` and
`κ(x) = κ(x₁) = κ(x₂)`. -/
@[stacks 0CBU "closing assertion: on a locally Noetherian k-scheme the conditions mean exactly \
two points of the normalization over x, with residue fields κ(x)"]
public theorem nonempty_quadraticAlgebra_algEquiv_prod_iff_normalizationFiber
    (k : Type u) [Field k] {X : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ AlgebraicGeometry.Spec (.of k)) (x : X)
    (hnodal :
      letI : Algebra k (X.presheaf.stalk x) := (fieldToStalk f x).hom.toAlgebra
      IsNodalAlgebra k (X.presheaf.stalk x)) :
    Nonempty (quadraticAlgebra (X.presheaf.stalk x) ≃ₐ[ResidueField (X.presheaf.stalk x)]
        (ResidueField (X.presheaf.stalk x) × ResidueField (X.presheaf.stalk x))) ↔
      Set.encard {x' : X.normalizationScheme (finite_irreducibleComponents_of_isCompact X) |
          X.normalization (finite_irreducibleComponents_of_isCompact X) x' = x} = 2 ∧
        ∀ x' : X.normalizationScheme (finite_irreducibleComponents_of_isCompact X),
          X.normalization (finite_irreducibleComponents_of_isCompact X) x' = x →
          Function.Bijective
            ((X.normalization (finite_irreducibleComponents_of_isCompact X)).residueFieldMap
              x').hom := by
  let : Algebra k (X.presheaf.stalk x) := (fieldToStalk f x).hom.toAlgebra
  have hbr := nonempty_quadraticAlgebra_algEquiv_prod_iff_numberOfBranches_eq_two k
    (X.presheaf.stalk x) hnodal
  rw [← numberOfBranches_eq_numberOfBranchesOfLocalRing,
    numberOfBranches_eq_encard_normalizationFiber X (finite_irreducibleComponents_of_isCompact X)
      x] at hbr
  refine ⟨fun hsplit ↦ ⟨hbr.mp hsplit, fun x' hx' ↦ ?_⟩, fun h ↦ hbr.mpr h.1⟩
  exact bijective_residueFieldMap_normalization_of_nonempty_algEquiv_prod
    (finite_irreducibleComponents_of_isCompact X) x hnodal.2.1 hsplit x' hx'

end Stacks.Curves

end
