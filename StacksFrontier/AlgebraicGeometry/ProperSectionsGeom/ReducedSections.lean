module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Etale.Field
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.Separable

/-!
# Global functions on a reduced proper scheme over a field

Let `X` be a proper scheme over a field `k`. Then `Γ(X, 𝒪_X)` is a finite-dimensional
`k`-algebra, and if `X` is reduced it is a finite product of finite field extensions of `k`. If
`X` is moreover geometrically reduced those extensions are separable, so `Γ(X, 𝒪_X)` is a finite
etale `k`-algebra.

These are clauses (1) and (3) of [Stacks, Tag 0BUG], and the etale packaging of (1), (3) and (4)
together. The remaining clause used here, separability of the factors, is (4), already carried by
`Stacks.AlgebraicGeometry.ProperSectionsGeom.GlobalSectionsFieldDecomposition.factor_isSeparable`
over a `GlobalSectionsFieldDecomposition`; this file supplies that decomposition for a reduced
`X`, so the two combine with nothing left over.

## Main results

All of these live in the namespace `Stacks.AlgebraicGeometry.ProperSectionsGeom`.

* `finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections`: the `k`-linear content of
  the degree-zero identification, as an equality `dim_k H⁰(X, 𝒪_X) = dim_k Γ(X, 𝒪_X)` of
  dimensions. Needs no properness, and is the public form of the comparison that
  `AlgebraicGeometry.cohomologyOverFieldZeroEquivSections`, being a bare `Equiv`, cannot give.
* `moduleFinite_globalSections_of_isProper`: clause (1). `Γ(X, 𝒪_X)` is a finite `k`-module, for
  an arbitrary proper morphism to the spectrum of a field.
* `globalSectionsFieldDecomposition_of_isReduced`: clause (3). For `X` reduced, a presentation of
  `Γ(X, 𝒪_X)` as a finite product of finite field extensions of `k`.
* `etale_globalSections_of_geometricallyReduced`: for `X` geometrically reduced, `Γ(X, 𝒪_X)` is a
  finite etale `k`-algebra.

## Implementation notes

**Clause (1).** Finiteness of coherent cohomology over a field is proved, for an arbitrary proper
morphism and every coherent module, as
`AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_isProper`; the structure sheaf is
coherent because a scheme proper over a field is locally Noetherian
(`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian` and
`AlgebraicGeometry.structureSheaf_isCoherent`). What has to be supplied is the identification of
degree-zero cohomology with sections, `k`-linearly. `AlgebraicGeometry.cohomologyOverField` is
by definition a restriction of scalars applied to the zeroth right derived functor of
`SheafOfModules.evaluation X.ringCatSheaf (op ⊤)`, and global sections are left exact, so
`CategoryTheory.Functor.rightDerivedZeroIsoSelf` at that functor gives the identification
directly; `zeroIsoSections` below is that composite. The public
`AlgebraicGeometry.cohomologyOverFieldZeroEquivSections` is deliberately a bare `Equiv` of types
-- its own documentation explains that `Γ(ℱ, ⊤)` carries no `Module k` structure of its own --
and finite dimensionality does not travel along an `Equiv`; the `k`-linear form is
`AlgebraicGeometry.cohomologyOverFieldZeroIsoSections`, which lives next to that `Equiv` in
`StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic` and is what both
`finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections` and clause (1) below are proved
from. The bridge it rests on is that the `Module k` structure that `RingHom.toAlgebra` puts on
`Γ(X, ⊤)` and the one `ModuleCat.restrictScalars` puts on it are the same restriction of scalars
along `k ⟶ Γ(X, ⊤)`, so `LinearEquiv.finrank_eq` applies with no transport.

**Clause (3).** A module-finite algebra over a field is Artinian, and an Artinian reduced ring is
the product of its residue fields (`IsArtinianRing.equivPi`). Reducedness of `Γ(X, 𝒪_X)` is
inherited from `X`. The product is reindexed along `Finite.equivFin` to the `Fin`-indexed shape
that `GlobalSectionsFieldDecomposition` asks for, and each factor is finite over `k` as a
quotient of a finite module.

**The etale packaging.** Mathlib characterizes an etale algebra over a field as a finite product
of finite separable field extensions (`Algebra.Etale.iff_exists_algEquiv_prod`). Clause (3)
supplies the product, clause (4) the separability of its factors; a geometrically reduced scheme
over a field is reduced, so clause (3) applies.

## References

* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

attribute [local instance] IsArtinianRing.fieldOfSubtypeIsMaximal

namespace Stacks.AlgebraicGeometry.ProperSectionsGeom

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The dimension of degree-zero cohomology of the structure sheaf is the dimension of the ring
of global functions**, for the `k`-algebra structure the structure morphism induces.

This is `AlgebraicGeometry.finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections` of
`StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic`, where the `k`-linear form
`AlgebraicGeometry.cohomologyOverFieldZeroIsoSections` of the degree-zero identification of
cohomology with sections lives; it is restated here under the name clause (1) of
[Stacks, Tag 0BUG] is proved from below. -/
theorem finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections :
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    Module.finrank k (cohomologyOverField k f (_root_.SheafOfModules.unit X.ringCatSheaf) 0) =
      Module.finrank k Γ(X, ⊤) :=
  AlgebraicGeometry.finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections k f

/-- **[Stacks, Tag 0BUG] (1).** The ring of global functions on a scheme proper over a field `k`
is a finite `k`-module, for the `k`-algebra structure the structure morphism induces.

No hypothesis beyond properness: the scheme need not be integral, connected, normal or reduced,
and the structure morphism need not be affine. -/
@[stacks 0BUG "clause (1): the global sections of an arbitrary proper scheme over a field form \
a finite module over that field, with no integrality, connectedness, normality, reducedness or \
affineness hypothesis. Finiteness of coherent cohomology over a field (Tag 02O6) plus coherence \
of the structure sheaf (Tag 01XZ), with the degree-zero identification of cohomology and \
sections supplied here from left exactness of global sections."]
theorem moduleFinite_globalSections_of_isProper [IsProper f] :
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    Module.Finite k Γ(X, ⊤) := by
  let alg : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := finiteDimensional_cohomologyOverField_of_isProper k f
    (_root_.SheafOfModules.unit X.ringCatSheaf) 0
  let iso := AlgebraicGeometry.cohomologyOverFieldZeroIsoSections k f
    (_root_.SheafOfModules.unit X.ringCatSheaf)
  exact Module.Finite.of_surjective iso.hom.hom (ConcreteCategory.bijective_of_isIso iso.hom).2

/-- **[Stacks, Tag 0BUG] (3).** The ring of global functions on a *reduced* scheme proper over a
field `k` is a finite product of finite field extensions of `k`.

The hypothesis is reducedness of `X`, weaker than the normality assumed by
`AlgebraicGeometry.globalSectionsFieldDecomposition_of_isNormal`, which this supersedes. -/
@[stacks 0BUG "clause (3): for a REDUCED proper scheme over a field, the presentation of the \
global sections as a finite product of finite field extensions of the base field. Clause (1) \
makes the ring Artinian; an Artinian reduced ring is the product of its residue fields. \
Reducedness only, where the library's normal-case decomposition needs each connected component \
irreducible. Separability of the factors is clause (4) and is not asserted here."]
def globalSectionsFieldDecomposition_of_isReduced [IsProper f] [IsReduced X] :
    GlobalSectionsFieldDecomposition k X f :=
  letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  haveI : Module.Finite k Γ(X, ⊤) := moduleFinite_globalSections_of_isProper k f
  haveI : IsArtinianRing Γ(X, ⊤) := isArtinian_of_tower k inferInstance
  let e := (Finite.equivFin (MaximalSpectrum Γ(X, ⊤))).symm
  { numFactors := Nat.card (MaximalSpectrum Γ(X, ⊤))
    factor := fun i => CommAlgCat.of k (Γ(X, ⊤) ⧸ (e i).asIdeal)
    factorIsField := fun _ => Field.toIsField _
    factorModuleFinite := fun i =>
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ k (e i).asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    algEquiv := ((IsArtinianRing.equivPi Γ(X, ⊤)).restrictScalars k).trans
      (AlgEquiv.piCongrLeft k (fun m : MaximalSpectrum Γ(X, ⊤) => Γ(X, ⊤) ⧸ m.asIdeal) e).symm }

/-- **The global functions on a geometrically reduced proper scheme over a field form a finite
etale algebra over that field.**

This is clauses (1), (3) and (4) of [Stacks, Tag 0BUG] combined: the global sections are a finite
product of field extensions of `k`, each finite and -- `X` being geometrically reduced --
separable, which is Mathlib's criterion for an etale algebra over a field. -/
theorem etale_globalSections_of_geometricallyReduced [IsProper f] [GeometricallyReduced f] :
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    Algebra.Etale k Γ(X, ⊤) ∧ Module.Finite k Γ(X, ⊤) := by
  let alg : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  have hXred : IsReduced X := AlgebraicGeometry.self_of_isIntegral_of_geometrically
    (P := IsReduced) (inferInstance : GeometricallyReduced f).geometrically_isReduced
  have hfin : Module.Finite k Γ(X, ⊤) := moduleFinite_globalSections_of_isProper k f
  have : IsArtinianRing Γ(X, ⊤) := isArtinian_of_tower k inferInstance
  let D := globalSectionsFieldDecomposition_of_isReduced k f
  let e := (Finite.equivFin (MaximalSpectrum Γ(X, ⊤))).symm
  refine ⟨(Algebra.Etale.iff_exists_algEquiv_prod k Γ(X, ⊤)).mpr
    ⟨MaximalSpectrum Γ(X, ⊤), inferInstance, fun m => Γ(X, ⊤) ⧸ m.asIdeal, inferInstance,
      inferInstance, (IsArtinianRing.equivPi Γ(X, ⊤)).restrictScalars k,
      fun m => ⟨?_, ?_⟩⟩, hfin⟩
  · infer_instance
  · have hs := GlobalSectionsFieldDecomposition.factor_isSeparable k f D (e.symm m)
    have he : e (e.symm m) = m := Equiv.apply_symm_apply e m
    rw [← he]
    exact hs

end Stacks.AlgebraicGeometry.ProperSectionsGeom

end
