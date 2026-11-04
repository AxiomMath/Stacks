module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkResidueFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupportEquality
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportClosedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportGeometricStalkCriterion

/-!
# The support of a finite type quasi-coherent module on an algebraic space

Let `X` be an algebraic space over a scheme `S` and let `F` be a quasi-coherent `𝒪_X`-module of
finite type.  Stacks 07TZ collects three facts about the support of `F` in the sense of
Stacks 04KA:

1. the support is closed in the point set of `X`;
2. for a geometric point `x̄` lying over a point `x` of `X`,
   `x ∈ Supp(F) ↔ F_{x̄} ≠ 0 ↔ F_{x̄} ⊗_{𝒪_{X, x̄}} κ(x̄) ≠ 0`;
3. for every morphism of algebraic spaces `g : X' ⟶ X` the pullback `g^* F` is again of finite
   type and `Supp(g^* F) = |g|^{-1}(Supp(F))`.

Each of the five conclusions is proved elsewhere in this development, at hypotheses no stronger
than the ones the source assumes; this module only puts them together into the single statement
the tag makes, so that the whole of 07TZ is one declaration.

## Main results

* `AlgebraicGeometry.Space.supportOfSheaf_of_isQuasicoherentOnSite_isFiniteTypeOnSite` is the
  whole of **Stacks 07TZ**.

## Implementation notes

The three clauses come from, in order,
`AlgebraicGeometry.Space.isClosed_supportOfSheaf_of_isFiniteTypeOnSite` (which needs only
finite type, not quasi-coherence),
`AlgebraicGeometry.Space.mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk_of_liesOver`
together with
`AlgebraicGeometry.Space.nontrivial_geometricModuleStalk_iff_nontrivial_residueFibre`, and
`AlgebraicGeometry.Space.isFiniteTypeOnSite_modulePullback` together with
`AlgebraicGeometry.Space.supportOfSheaf_modulePullback_eq`.

The support of Stacks 04KA is defined by nonvanishing of the stalk at *some* geometric point
over the given point, so the first equivalence of clause (2) is not a definitional unfolding:
its content is that for a quasi-coherent module *every* geometric point over a point of the
support detects it.  For the same reason clause (2) is stated for an arbitrary geometric point
lying over an arbitrary point, which is how the source states it.

The statement is at module universe `m = u`, that is for
`AlgebraicGeometry.Space.Modules.{u, u}`, because clauses (2) and (3) are available only there:
both rest on the finiteness of the geometric stalk, which is read off the sections over an
affine étale chart.

## References

* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 04KG](https://stacks.math.columbia.edu/tag/04KG)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 07TZ.** Let `X` be an algebraic space over a scheme `S` and let `F` be a
quasi-coherent `𝒪_X`-module of finite type.  Then

1. the support of `F` is closed;
2. for a geometric point `x̄` of `X` lying over a point `x`,
   `x ∈ Supp(F) ↔ F_{x̄} ≠ 0` and `F_{x̄} ≠ 0 ↔ F_{x̄} ⊗_{𝒪_{X, x̄}} κ(x̄) ≠ 0`;
3. for every morphism `g : X' ⟶ X` of algebraic spaces over `S` the pullback `g^* F` of
   Stacks 03LU is again of finite type and `Supp(g^* F) = |g|^{-1}(Supp(F))`.

Clause (1) is `AlgebraicGeometry.Space.isClosed_supportOfSheaf_of_isFiniteTypeOnSite`, which
does not use quasi-coherence.  The two equivalences of clause (2) are
`AlgebraicGeometry.Space.mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk_of_liesOver`
and `AlgebraicGeometry.Space.nontrivial_geometricModuleStalk_iff_nontrivial_residueFibre`.  The
two conclusions of clause (3) are
`AlgebraicGeometry.Space.isFiniteTypeOnSite_modulePullback` and
`AlgebraicGeometry.Space.supportOfSheaf_modulePullback_eq`. -/
@[stacks 07TZ]
theorem supportOfSheaf_of_isQuasicoherentOnSite_isFiniteTypeOnSite
    (X : AlgebraicSpaces B S hS) (F : Modules.{u, u} B S hS X.1 X.2)
    (hqc : F.IsQuasicoherentOnSite) (hft : SheafOfModules.IsFiniteTypeOnSite F) :
    IsClosed (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F)) ∧
      (∀ (x : GeometricPoint B S hS X.1) (pt : points B S hS X.1), x.LiesOver pt →
        (pt ∈ supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) ↔
            Nontrivial (geometricModuleStalk B S hS X x F)) ∧
          (Nontrivial (geometricModuleStalk B S hS X x F) ↔
            letI := isLocalRing_etaleLocalRing B S hS X.1 X.2 x
            Nontrivial (geometricModuleResidueFibre B S hS X x F))) ∧
      ∀ (X' : AlgebraicSpaces B S hS) (g : X' ⟶ X),
        SheafOfModules.IsFiniteTypeOnSite ((modulePullback B S hS g).obj F) ∧
          supportOfSheaf B S hS X'.1
              ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS g).obj F)) =
            pointsMap B S hS X'.1 g.hom ⁻¹'
              supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) := by
  refine ⟨?_, fun x pt hx => ⟨?_, ?_⟩, fun X' g => ⟨?_, ?_⟩⟩
  · exact have := hft
      isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X.1 X.property F
  · exact have := hqc
      mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk_of_liesOver B S hS X F x pt hx
  · exact nontrivial_geometricModuleStalk_iff_nontrivial_residueFibre B S hS X F hqc hft x
  · exact isFiniteTypeOnSite_modulePullback B S hS g F hft
  · exact supportOfSheaf_modulePullback_eq B S hS g F hqc hft

end AlgebraicGeometry.Space

end
