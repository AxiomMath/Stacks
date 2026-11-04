module

public import StacksFrontier.AlgebraicGeometry.Curves.NodalDichotomy
public import StacksFrontier.AlgebraicGeometry.Curves.NodeBaseChangeFibre
public import StacksFrontier.AlgebraicGeometry.Curves.NodeBranchResiduesGlobal
public import StacksFrontier.AlgebraicGeometry.Curves.NodeDerivationExtensionLocal
public import StacksFrontier.AlgebraicGeometry.UnitsNormalProper.Japanese

/-!
# Extending a derivation at a maximal ideal of an affine open of a nodal curve

Let `k` be an algebraically closed field and `X` a reduced one-dimensional `k`-scheme, locally of
finite type, whose singularities are at worst nodal. Let `U ⊆ X` be an affine open and `P` a
maximal ideal of `Γ(X, U)`. Then every `k`-derivation of `Γ(X, U)_P` extends to the integral
closure of `Γ(X, U)_P` in its total ring of fractions.

## Main results

* `Stacks.Curves.isNagataRing_localization_atPrime_of_finiteType`: a localization of a
  finite-type algebra over a field at a prime is a Nagata ring.
* `Stacks.Curves.exists_extend_integralClosure_of_isRegularLocalRing_or_isNodalAlgebra`: a
  `k`-derivation of a Nagata local `k`-algebra with residue field `k` which is regular or nodal
  extends to the integral closure in the total ring of fractions.
* `Stacks.Curves.exists_mem_nonempty_ringEquiv_stalk_localization`: a prime of the coordinate
  ring of an affine open is a point of that open whose stalk is, as a ring, the localization at
  that prime.
* `Stacks.Curves.exists_extend_integralClosure_localization_of_hasAtWorstNodalSingularities`: at
  every maximal ideal of the coordinate ring of an affine open of an at-worst-nodal curve a
  `k`-derivation extends to the integral closure in the total ring of fractions.
* `exists_extend_integralClosure_localization_structMapLE_of_hasAtWorstNodalSingularities`: the
  same, for the `k`-algebra structure on `Γ(X, U)` given by the structure morphism.

## References

* [Stacks Project, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68)
* [Stacks Project, Tag 0C47](https://stacks.math.columbia.edu/tag/0C47)
* [Stacks Project, Tag 032U](https://stacks.math.columbia.edu/tag/032U)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing Topology
open Stacks.AlgebraicGeometry.UnitsNormalProper

universe u v

namespace Stacks.Curves

/-- A localization of a finite-type algebra over a field at a prime is a Nagata ring. -/
public theorem isNagataRing_localization_atPrime_of_finiteType (k : Type u) (A : Type u)
    [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] (P : Ideal A) [P.IsPrime] :
    IsNagataRing (Localization.AtPrime P) := by
  have h12 : IsNagataRing k → ∀ (S : Type u) [CommRing S] [Algebra k S]
      [Algebra.FiniteType k S], IsNagataRing S := ((isNagataRing_tfae (R := k)).out 1 2).mp
  exact isNagata_of_isLocalization A P.primeCompl (Localization.AtPrime P)
    (h12 IsNagataRing.of_field A)

/-- A `k`-derivation of a Nagata local `k`-algebra with residue field `k` which is either regular
or nodal extends to the integral closure in the total ring of fractions. -/
public theorem exists_extend_integralClosure_of_isRegularLocalRing_or_isNodalAlgebra
    (k : Type u) (A : Type v) [Field k] [IsAlgClosed k] [CommRing A] [IsLocalRing A] [Algebra k A]
    (hNagata : IsNagataRing A) (eκ : ResidueField A ≃ₐ[k] k)
    (hA : IsRegularLocalRing A ∨ IsNodalAlgebra k A) (D : Derivation k A A) :
    ∃ E : Derivation k ↥(integralClosure A (FractionRing A))
        ↥(integralClosure A (FractionRing A)),
      ∀ a : A, E (algebraMap A ↥(integralClosure A (FractionRing A)) a)
        = algebraMap A ↥(integralClosure A (FractionRing A)) (D a) := by
  rcases hA with hreg | hnodal
  · exact exists_extend_integralClosure_of_isRegularLocalRing k A D
  · exact exists_extend_integralClosure_of_isNodalAlgebra_residueField k A hNagata hnodal eκ D

/-- For a prime `P` of the coordinate ring of an affine open `U`, there is a point `x ∈ U` whose
stalk is isomorphic, as a ring, to the localization of `Γ(X, U)` at `P`. -/
public theorem exists_mem_nonempty_ringEquiv_stalk_localization {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (P : Ideal Γ(X, U)) [hP : P.IsPrime] :
    ∃ x : X, x ∈ U ∧ Nonempty (X.presheaf.stalk x ≃+* Localization.AtPrime P) := by
  have hy : hU.fromSpec ⟨P, hP⟩ ∈ U := hU.range_fromSpec.le (Set.mem_range_self _)
  refine ⟨hU.fromSpec ⟨P, hP⟩, hy, ?_⟩
  let : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec ⟨P, hP⟩)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨hU.fromSpec ⟨P, hP⟩, hy⟩ : ↥U)
  have : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec ⟨P, hP⟩)) P :=
    hU.isLocalization_stalk' ⟨P, hP⟩ hy
  exact ⟨(IsLocalization.algEquiv P.primeCompl
    (X.presheaf.stalk (hU.fromSpec ⟨P, hP⟩)) (Localization.AtPrime P)).toRingEquiv⟩

/-- At every maximal ideal `P` of the coordinate ring of an affine open `U` of an at-worst-nodal
curve over `k`, every `k`-derivation of `Γ(X, U)_P` extends to the integral closure of `Γ(X, U)_P`
in its total ring of fractions, for any `k`-algebra structure on `Γ(X, U)` agreeing with the
structure morphism. -/
public theorem exists_extend_integralClosure_localization_of_hasAtWorstNodalSingularities
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) [IsReduced X]
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {U : X.Opens} (hU : IsAffineOpen U) (P : Ideal Γ(X, U)) [P.IsMaximal]
    [Algebra k Γ(X, U)]
    (halg : ∀ c : k, algebraMap k Γ(X, U) c = structMapLE (X ↘ Spec (.of k)) U c)
    (D : Derivation k (Localization.AtPrime P) (Localization.AtPrime P)) :
    ∃ E : Derivation k
        ↥(integralClosure (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)))
        ↥(integralClosure (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))),
      ∀ a : Localization.AtPrime P, E (algebraMap _ _ a) = algebraMap _ _ (D a) := by
  have hft : Algebra.FiniteType k Γ(X, U) := by
    refine RingHom.finiteType_algebraMap.mp ?_
    rw [show algebraMap k Γ(X, U) = structMapLE (X ↘ Spec (.of k)) U from RingHom.ext halg]
    exact finiteType_structMapLE (X ↘ Spec (.of k)) ⟨U, hU⟩
  have hNagata : IsNagataRing (Localization.AtPrime P) :=
    isNagataRing_localization_atPrime_of_finiteType k Γ(X, U) P
  have : IsNoetherianRing (Localization.AtPrime P) := hNagata.isNoetherianRing
  obtain ⟨eκ⟩ := nonempty_residueField_localization_algEquiv_of_isAlgClosed k Γ(X, U) P
  obtain ⟨x, -, ⟨e⟩⟩ := exists_mem_nonempty_ringEquiv_stalk_localization hU P
  have : IsNoetherianRing (X.presheaf.stalk x) :=
    isNoetherianRing_of_ringEquiv (Localization.AtPrime P) e.symm
  refine exists_extend_integralClosure_of_isRegularLocalRing_or_isNodalAlgebra k
    (Localization.AtPrime P) hNagata eκ ?_ D
  rcases isRegularLocalRing_stalk_or_isNode_of_hasAtWorstNodalSingularities k X hdim hnodal x with
    hreg | hnode
  · exact Or.inl (IsRegularLocalRing.of_ringEquiv e)
  · let : Algebra k (X.presheaf.stalk x) :=
      (fieldToStalk (X ↘ Spec (.of k)) x).hom.toAlgebra
    exact Or.inr (isNodalAlgebra_of_ringEquiv k k e
      (((isNode_tfae_of_isClosed k X hdim x hnode.1).out 1 2).mp hnode))

/-- At every maximal ideal `P` of the coordinate ring of an affine open `U` of an at-worst-nodal
curve over `k`, every `k`-derivation of `Γ(X, U)_P` extends to the integral closure of `Γ(X, U)_P`
in its total ring of fractions, where `Γ(X, U)` is a `k`-algebra through the structure
morphism. -/
public theorem
    exists_extend_integralClosure_localization_structMapLE_of_hasAtWorstNodalSingularities
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) [IsReduced X]
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {U : X.Opens} (hU : IsAffineOpen U) (P : Ideal Γ(X, U)) [P.IsMaximal] :
    letI : Algebra k Γ(X, U) := (structMapLE (X ↘ Spec (.of k)) U).toAlgebra
    ∀ D : Derivation k (Localization.AtPrime P) (Localization.AtPrime P),
      ∃ E : Derivation k
          ↥(integralClosure (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)))
          ↥(integralClosure (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))),
        ∀ a : Localization.AtPrime P, E (algebraMap _ _ a) = algebraMap _ _ (D a) := by
  let : Algebra k Γ(X, U) := (structMapLE (X ↘ Spec (.of k)) U).toAlgebra
  exact fun D ↦ exists_extend_integralClosure_localization_of_hasAtWorstNodalSingularities k X
    hdim hnodal hU P (fun _ ↦ rfl) D

end Stacks.Curves

end
