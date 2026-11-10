module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CountableExtQcqsEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CountableSectionsDerivedTensorPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTensor
import StacksCore.Tactic.StacksAttribute

/-!
# Countable cohomology and countable `Ext` over the qcqs étale objects of a space

Let `X` be a quasi-compact quasi-separated algebraic space over a scheme `S`, let `K` be an
object of `D_QCoh(𝒪_X)` whose cohomology sheaves have countable sets of sections over the affine
schemes étale over `X`, and let `E` be a perfect object of `D(𝒪_X)`. For every quasi-compact
quasi-separated étale `U ⟶ X` and every `i`, both `H^i(U, K ⊗^𝐋 E)` and `Ext^i(E|_U, K|_U)` are
countable. This file states the two conclusions together, for the canonical derived tensor
product `AlgebraicGeometry.Space.smallEtaleDerivedTensor` of the small étale site of `X`.

The two clauses are already theorems of the library, each with no hypothesis beyond the tag's
own once the derived tensor product is fixed:

* `AlgebraicGeometry.Space.hasCountableCohomology_derivedTensor_restrict_of_isPerfect`, for an
  arbitrary derived tensor product datum, read here at the canonical one
  `AlgebraicGeometry.Space.smallEtaleDerivedTensorProduct`;
* `AlgebraicGeometry.Space.countable_ext_of_qcqs_etale_of_countable_sections`, which runs the
  induction principle of Stacks 08GP directly on the `Ext` groups.

## Main results

* `AlgebraicGeometry.Space.countable_cohomology_derivedTensor_and_ext_of_qcqs_etale`: both
  clauses of Stacks 0CRU.

## Implementation notes

The derived categories in play are the standard models `HasDerivedCategory.standard`, which is
the model every input above is stated at; they are introduced by `letI` in the statement rather
than as a file-wide instance.

## References

* [Stacks Project, Tag 0CRU](https://stacks.math.columbia.edu/tag/0CRU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CRU.** Let `X` be a quasi-compact quasi-separated algebraic space over `S`, let `K`
be an object of `D_QCoh(𝒪_X)` such that the cohomology sheaves `H^q(K)` have countable sets of
sections over the affine schemes étale over `X`, and let `E` be a perfect object of `D(𝒪_X)`.
Then for every quasi-compact quasi-separated étale `U ⟶ X` and every `i : ℤ` the sets
`H^i(U, K ⊗^𝐋 E)` and `Ext^i(E|_U, K|_U)` are countable.

Here `U` is an object of the spaces-étale site of `X`, and quasi-compactness and
quasi-separatedness are those of `U` itself; since `X` is quasi-compact and quasi-separated these
are equivalent to quasi-compactness and quasi-separatedness of the morphism `U ⟶ X`.
`H^i(U, K ⊗^𝐋 E)` is the `i`-th cohomology of the derived global sections over `U` of the
restriction of `K ⊗^𝐋 E` to `U`, and `(-)|_U` is restriction of modules along the étale
`U ⟶ X`, read on derived categories.

The cohomology clause is
`AlgebraicGeometry.Space.hasCountableCohomology_derivedTensor_restrict_of_isPerfect` at the
canonical derived tensor product of the small étale site, and the `Ext` clause is
`AlgebraicGeometry.Space.countable_ext_of_qcqs_etale_of_countable_sections`. -/
@[stacks 0CRU]
theorem countable_cohomology_derivedTensor_and_ext_of_qcqs_etale
    (X : AlgebraicSpaces B S hS)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
    (∀ v : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 v → ∀ q : ℤ,
      Countable (((DerivedCategory.homologyFunctor
        (Modules.{u, u} B S hS X.1 X.2) q).obj K.obj).val.obj (op v))) →
    ∀ E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2),
      RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E →
    ∀ U : SpacesEtale B S hS X, IsQuasiCompactSpace B S hS U.1.left.1 →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal U.1.left.1 → ∀ i : ℤ,
      letI := HasDerivedCategory.standard (Modules.{u, u} B S hS U.1.left.1 U.1.left.2)
      letI := HasDerivedCategory.standard AddCommGrpCat.{u + 1}
      Countable ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} i).obj
          ((derivedGlobalSectionsAb B S hS U.1.left).obj
            ((etaleModulePullback.{u, u} B S hS U.1.hom U.2).mapDerivedCategory.obj
              (((smallEtaleDerivedTensor B S hS X).obj K.obj).obj E)))) ∧
        Countable (DerivedCategory.Ext
          ((etaleModulePullback.{u, u} B S hS U.1.hom U.2).mapDerivedCategory.obj E)
          ((etaleModulePullback.{u, u} B S hS U.1.hom U.2).mapDerivedCategory.obj K.obj) i) := by
  intro hK E hE U hUqc hUqs i
  exact ⟨hasCountableCohomology_derivedTensor_restrict_of_isPerfect B S hS (X := X)
      B.contains_terminal (smallEtaleDerivedTensorProduct B S hS X) K.obj K.property
      hK E hE U hUqc hUqs i,
    countable_ext_of_qcqs_etale_of_countable_sections X K hK E hE U hUqc hUqs i⟩

end AlgebraicGeometry.Space

end
