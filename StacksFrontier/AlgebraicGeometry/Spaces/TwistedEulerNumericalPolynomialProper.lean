module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSchemeTheoreticSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.EulerCharacteristicAdditivity
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedTwistedCohomology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The twisted Euler characteristics on a proper algebraic space are a numerical polynomial

Let `k` be a field, `X` a proper algebraic space over `k`, `F` a coherent `𝒪_X`-module and
`L₁, …, L_r` invertible `𝒪_X`-modules.  Stacks 0DN4 says that

`(n₁, …, n_r) ↦ χ(X, F ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_r^{⊗ n_r})`

is a numerical polynomial of total degree at most the dimension of the scheme-theoretic support
of `F`.  This file proves it, in two forms:

* `AlgebraicGeometry.Space.isTwistedEulerNumericalPolynomial_of_isCoherent`: the library's
  statement `AlgebraicGeometry.Space.IsTwistedEulerNumericalPolynomial` — for every closed subspace
  `i : Z ⟶ X` with `F ≅ i_*𝒢`, the degree is at most `dim Z`;
* `AlgebraicGeometry.Space.hasTwistedEulerPolynomialOfDegreeLE_coherentSchemeTheoreticSupport`:
  the bound by the dimension of the scheme-theoretic support of `F` itself (Stacks 07U0, 07UG).

The polynomial is rational with integer values at the integral tuples
(`AlgebraicGeometry.Space.exists_intCast_eq_eval_of_representsTwistedEuler`), which is what
"numerical" means (Stacks 027X), and it is unique
(`AlgebraicGeometry.Space.eq_of_representsTwistedEuler`).  When the support is empty the bound is
`⊥` and the polynomial is `0`, the convention of
`AlgebraicGeometry.Space.HasTwistedEulerPolynomialOfDegreeLE`.

## The proof

This is the source's.  The scheme-theoretic support `Z` of `F` carries a coherent `𝒢` with
`F ≅ i_*𝒢`, and the dévissage of Stacks 08AN is run on `Z`
(`AlgebraicGeometry.Space.hasTwistedEulerPolynomialAlong_of_isCoherent`): conditions (1) and (2)
follow from the additivity of the twisted Euler characteristics (Stacks 0DN2,
`AlgebraicGeometry.Space.hasAdditiveTwistedEulerOnCoherent_of_isProper`), and condition (3) is the
witness built from Chow's lemma
(`AlgebraicGeometry.Space.hasCoherentWitnessOnIntegralSubspaces_hasTwistedEulerPolynomialAlong`),
whose twisted Euler characteristics are those of a twist of an invertible module on a scheme proper
over `k`, polynomial by the scheme case Stacks 0BEM.

## References

* [Stacks Project, Tag 0DN4](https://stacks.math.columbia.edu/tag/0DN4)
* [Stacks Project, Tag 0DN2](https://stacks.math.columbia.edu/tag/0DN2)
* [Stacks Project, Tag 08AN](https://stacks.math.columbia.edu/tag/08AN)
* [Stacks Project, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM)
* [Stacks Project, Tag 07U0](https://stacks.math.columbia.edu/tag/07U0)
* [Stacks Project, Tag 07UG](https://stacks.math.columbia.edu/tag/07UG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Space

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (X : AlgebraicSpaces B (Spec (.of k)) hk) {r : ℕ}
    (f : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hf : IsProper B (Spec (.of k)) hk f)

/-- **Stacks 0DN4.**  Let `k` be a field, `X` a proper algebraic space over `k`, `F` a coherent
`𝒪_X`-module and `L₁, …, L_r` invertible `𝒪_X`-modules.  For every closed subspace `i : Z ⟶ X`
with `F ≅ i_*𝒢` for a coherent `𝒪_Z`-module `𝒢`, the twisted Euler characteristics
`χ(X, F ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_r^{⊗ n_r})` are the values at the integral tuples of a rational
polynomial which is zero or of total degree at most `dim Z`.  Taking `Z` to be the
scheme-theoretic support of `F` is
`AlgebraicGeometry.Space.hasTwistedEulerPolynomialOfDegreeLE_coherentSchemeTheoreticSupport`. -/
@[stacks 0DN4 "for every closed subspace Z with F = i_*G, G coherent; the scheme-theoretic support \
is the smallest such Z (Stacks 07U0), and the bound at it is \
hasTwistedEulerPolynomialOfDegreeLE_coherentSchemeTheoreticSupport", sga "6 X 2.3.1" "more general"]
theorem isTwistedEulerNumericalPolynomial_of_isCoherent
    (F : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    (hF : IsCoherent B (Spec (.of k)) hk X.1 X.2 F)
    (L : Fin r → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O)).property (L j)] :
    @IsTwistedEulerNumericalPolynomial.{u, w} k _ B hk X r f hf F L _
      (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L F hF) :=
  isTwistedEulerNumericalPolynomial_of_witness
    (hasAdditiveTwistedEulerOnCoherent_of_isProper.{u, w} k B hk X f hf L)
    (fun Z i hi => hasCoherentWitnessOnIntegralSubspaces_hasTwistedEulerPolynomialAlong.{u, w}
      k B hk X f hf L Z i hi (representedTwistedCohomologyComparison k B hk)) F hF

/-- **Stacks 0DN4.**  Let `k` be a field, `X` a proper algebraic space over `k`, `F` a coherent
`𝒪_X`-module and `L₁, …, L_r` invertible `𝒪_X`-modules.  The map
`(n₁, …, n_r) ↦ χ(X, F ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_r^{⊗ n_r})` is the restriction to the integral tuples
of a rational polynomial which is zero or of total degree at most the dimension of the
scheme-theoretic support of `F`.  It is numerical, its values being integers
(`AlgebraicGeometry.Space.exists_intCast_eq_eval_of_representsTwistedEuler`), and unique
(`AlgebraicGeometry.Space.eq_of_representsTwistedEuler`); when the support is empty it is `0`.

`F` is the direct image of a coherent module on its scheme-theoretic support (Stacks 07U0 and
07UG), and `AlgebraicGeometry.Space.isTwistedEulerNumericalPolynomial_of_isCoherent` applies. -/
@[stacks 0DN4]
theorem hasTwistedEulerPolynomialOfDegreeLE_coherentSchemeTheoreticSupport
    (F : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2) [hF : IsCoherent B (Spec (.of k)) hk X.1 X.2 F]
    (L : Fin r → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O)).property (L j)] :
    @HasTwistedEulerPolynomialOfDegreeLE.{u, w} k _ B hk X r f hf F L _
      (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L F hF)
      (dimension B (Spec (.of k)) hk
        (closedSubspaceToSpace B (Spec (.of k)) hk X
          (coherentSchemeTheoreticSupport B (Spec (.of k)) hk X F)).1
        (closedSubspaceToSpace B (Spec (.of k)) hk X
          (coherentSchemeTheoreticSupport B (Spec (.of k)) hk X F)).2) := by
  have hXN := hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk X.1 X.2 f hf
  have : SheafOfModules.IsCoherentOnSite F := hF.toIsCoherentOnSite
  have hft := isFiniteTypeOnSite_of_isCoherentOnSite B (Spec (.of k)) hk X F
  obtain ⟨hZ, G, hGqc, ⟨e⟩⟩ := exists_module_on_schemeTheoreticSupport B (Spec (.of k)) hk X F
    hF.toIsQuasicoherentOnSite
    (Stacks.SheafOfModules.presheafIsFiniteType_of_isFiniteTypeOnSite _ hft)
  have hG := isCoherent_module_on_coherentSchemeTheoreticSupport B (Spec (.of k)) hk X hXN F G
    hGqc e
  exact isTwistedEulerNumericalPolynomial_of_isCoherent k B hk X f hf F hF L
    _ _ (coherentSchemeTheoreticSupport B (Spec (.of k)) hk X F).2.2 G hG e.symm

end AlgebraicGeometry.Space

end
