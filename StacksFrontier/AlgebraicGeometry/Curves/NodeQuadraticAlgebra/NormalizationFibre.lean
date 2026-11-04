module

public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.Node.Algebra
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Henselization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.LocalPullback
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.Topology.Dimension.DimensionFunctionObstruction
public import StacksFrontier.Topology.Noetherian.QuasiCompactLocally

/-!
# The fibre of the normalization at a node

Let `x` be a node on a locally Noetherian scheme `X` over a field. The fibre of the
normalization of `X` over `x` is the spectrum of the quadratic algebra associated to the local
ring at `x`, as a scheme over the residue field of `x`.

The two sides are compared through the base change of the normalization along
`Spec 𝒪_{X,x} ⟶ X`, which is the spectrum of the integral closure `N` of `𝒪_{X,x}` in the
product of the residue fields of its minimal primes. Base changing once more along
`Spec κ ⟶ Spec 𝒪_{X,x}` gives `Spec (κ ⊗ N)`, and the quadratic algebra is the fibre
`C ⧸ 𝔪 C` of the integral closure `C` of `𝒪_{X,x}` in its total ring of fractions. The
identification of the two is purely algebraic: `N` and `C` agree because the local ring at a
node is reduced, so the product of the minimal-prime residue fields *is* the total ring of
fractions; and `κ ⊗ C` is `C ⧸ 𝔪 C` by the base change of a quotient.

## Main definitions

There are no public definitions.

## Main results

* `Stacks.Curves.quadraticAlgebraSpecIsoNormalizationFiber` — the spectrum of the quadratic
  algebra of the local ring at a node is the fibre of the normalization over that node, as a
  scheme over the residue field.

## Implementation notes

The equality of schemes in the source is expressed as an isomorphism in the category of schemes
over the spectrum of the residue field, so that it carries the information that the
identification is one of fibres and not merely of abstract schemes.

The local algebra at `x` is represented directly by the stalk `𝒪_{X,x}` rather than by an
abstract local algebra, and its residue field by the scheme's residue field at `x`; local
Noetherianity of `X` supplies, through Stacks 01OZ and 04ZB, the finiteness of the irreducible
components of quasi-compact opens that the normalization construction of Stacks 035N takes as a
hypothesis.

Base change is performed in two steps rather than one. The first step is Stacks 0C3B's local
description of the normalization, which is already available; the second is the purely formal
`AlgebraicGeometry.pullback_baseChange_spec`, which turns an isomorphism
`Y ×_X Spec A ≅ Spec N` compatible with the projection into an isomorphism
`Y ×_X Spec B ≅ Spec (B ⊗[A] N)` over `Spec B` for any `A`-algebra `B`. It needs nothing of the
normalization and is stated for an arbitrary morphism.

## References

* [Stacks Project, Tag 0CBT](https://stacks.math.columbia.edu/tag/0CBT)
* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
* [Stacks Project, Tag 035N](https://stacks.math.columbia.edu/tag/035N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Stacks.Curves

/-- `Spec` of an algebra equivalence is compatible with the structure morphisms. -/
private theorem specMapIso_algMap {R B C : Type u}
    [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] (e : B ≃ₐ[R] C) :
    (Scheme.Spec.mapIso e.toCommRingCatIso.op).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R B)) =
      Spec.map (CommRingCat.ofHom (algebraMap R C)) := by
  show Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R B)) =
    Spec.map (CommRingCat.ofHom (algebraMap R C))
  rw [← Spec.map_comp]
  congr 1
  ext a
  exact e.commutes a

/-- An algebra equivalence induces an isomorphism of the spectra over the base. -/
private noncomputable def specOverIsoOfAlgEquiv {R B C : Type u}
    [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] (e : B ≃ₐ[R] C) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R C))) ≅
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B))) :=
  Over.isoMk (Scheme.Spec.mapIso e.toCommRingCatIso.op) (specMapIso_algMap e)

/-- The spectrum of the quadratic algebra associated to a node is the fibre of the
normalization over that node. -/
@[stacks 0CBT "normalization_fibre"]
public theorem quadraticAlgebraSpecIsoNormalizationFiber
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [IsLocallyNoetherian X] (x : X)
    (hnode :
      let kToStalk : k →+* X.presheaf.stalk x :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom
      letI : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
      IsNodalAlgebra k (X.presheaf.stalk x)) :
    let hX : ∀ U : X.Opens, IsCompact (U : Set X) →
        (irreducibleComponents U).Finite := fun U hU ↦ by
      let : CompactSpace U := isCompact_iff_compactSpace.mp hU
      let : NoetherianSpace U :=
        noetherianSpace_of_isLocallyNoetherianSpace U
          ((isLocallyNoetherianSpace_of_isLocallyNoetherian X).subtype U)
      exact NoetherianSpace.finite_irreducibleComponents
    letI : Algebra (X.residueField x)
        (quadraticAlgebra (X.presheaf.stalk x)) := by
      change Algebra (IsLocalRing.ResidueField (X.presheaf.stalk x))
        (quadraticAlgebra (X.presheaf.stalk x))
      infer_instance
    Nonempty
      (Over.mk (Spec.map (
        let A := X.presheaf.stalk x
        let B := integralClosure A (FractionRing A)
        let J := (IsLocalRing.maximalIdeal A).map (algebraMap A B)
        let f : A →+* (B ⧸ J) := (Ideal.Quotient.mk J).comp (algebraMap A B)
        let g : IsLocalRing.ResidueField A →+* (B ⧸ J) :=
          Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) f fun _a ha ↦
            Ideal.Quotient.eq_zero_iff_mem.mpr
              (Ideal.mem_map_of_mem (algebraMap A B) ha)
        let g' : @RingHom (IsLocalRing.ResidueField A) (B ⧸ J)
            (X.residueField x).commRing.toCommSemiring.toNonAssocSemiring
            (CommRingCat.of (B ⧸ J)).commRing.toCommSemiring.toNonAssocSemiring := {
          toFun := g
          map_one' := g.map_one
          map_mul' := g.map_mul
          map_zero' := g.map_zero
          map_add' := g.map_add }
        CommRingCat.ofHom g')) ≅
        Over.mk (pullback.snd (Scheme.normalization X hX)
          (X.fromSpecResidueField x))) := by
  intro hX
  let A := X.presheaf.stalk x
  let κ := A ⧸ IsLocalRing.maximalIdeal A
  let kToStalk : k →+* A :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom
  let : Algebra k A := kToStalk.toAlgebra
  have hA : IsNodalAlgebra k A := hnode
  let : IsReduced A := hA.2.1
  let : Algebra A κ := inferInstance
  let Dprod := minimalPrimes.residueFieldProduct A
  let : Algebra A Dprod := (minimalPrimes.residueFieldProductHom A).toAlgebra
  let N := integralClosure A Dprod
  let : Algebra A N := Subalgebra.algebra N
  obtain ⟨eNorm, heNorm⟩ := Scheme.exists_iso_pullback_normalization_fromSpecStalk X hX x
  obtain ⟨eBase⟩ := @pullback_baseChange_spec (X.presheaf.stalk x) κ N
    inferInstance inferInstance inferInstance (inferInstance : Algebra (X.presheaf.stalk x) κ)
    (inferInstance : Algebra (X.presheaf.stalk x) N) X (Scheme.normalizationScheme X hX)
    (Scheme.normalization X hX) (X.fromSpecStalk x) eNorm heNorm
  let S := κ ⊗[A] N
  let C := integralClosure A (FractionRing A)
  let D := C ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A C)
  let : Algebra A C := Subalgebra.algebra C
  let : Algebra A (Scheme.normalizationPushforwardStalk X hX x) :=
    Scheme.normalizationPushforwardStalkAlgebra X hX x
  -- Keep the canonical map from `A` into the fraction ring of its reduction in scope:
  -- the equivalence of normalization stalks below is stated using this particular
  -- algebra structure, which need not be definitionally the default localization one.
  let : Algebra A (FractionRing (A ⧸ nilradical A)) :=
    (Stacks.NormalizationStalkAmbient.reductionFractionRingHom A).toAlgebra
  let eFrac := Stacks.NormalizationStalkAmbient.fractionRingReductionAlgEquiv A hA.2.1
  let eN : N ≃ₐ[A] C :=
    (Scheme.normalizationPushforwardStalkEquivIntegralClosureMinimalPrimeResidueFields
      X hX x).symm.trans
      ((Scheme.normalizationPushforwardStalkEquivIntegralClosureReductionFractionRing X hX x).trans
        eFrac.mapIntegralClosure)
  let : CommRing S := Algebra.TensorProduct.instCommRing
  let : Algebra A S := Algebra.TensorProduct.instAlgebra
  let : CommRing (κ ⊗[A] C) := Algebra.TensorProduct.instCommRing
  let : Algebra A (κ ⊗[A] C) := Algebra.TensorProduct.instAlgebra
  let : IsScalarTower A A κ := IsScalarTower.of_algebraMap_eq fun _ => by simp
  let : SMulCommClass A κ κ := ⟨fun a b c => by simp only [Algebra.smul_def]; ring⟩
  let : Algebra κ S := Algebra.TensorProduct.leftAlgebra
  let : Algebra κ (κ ⊗[A] C) := Algebra.TensorProduct.leftAlgebra
  let eTensor : S ≃ₐ[κ] κ ⊗[A] C := Algebra.TensorProduct.congr AlgEquiv.refl eN
  let eQuot : D ≃ₐ[κ] κ ⊗[A] C :=
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor C (IsLocalRing.maximalIdeal A)
  have hbase : Spec.map (CommRingCat.ofHom (algebraMap A κ)) ≫ X.fromSpecStalk x =
      X.fromSpecResidueField x := by
    have hres : (algebraMap A κ) = (X.residue x).hom := IsLocalRing.ResidueField.algebraMap_eq A
    show _ = Spec.map (X.residue x) ≫ X.fromSpecStalk x
    rw [show CommRingCat.ofHom (algebraMap A κ) = X.residue x from CommRingCat.hom_ext hres]
    rfl
  rw [hbase] at eBase
  exact ⟨@specOverIsoOfAlgEquiv κ S D inferInstance inferInstance inferInstance
    inferInstance inferInstance (eTensor.trans eQuot.symm) ≪≫ eBase.symm⟩

end Stacks.Curves

end
