module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FlatLength
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Fiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.FiberMaximalIdeal
public import StacksCore.Tactic.StacksAttribute

/-!
# The canonical weighting of an étale morphism is identically one

Let `j : U ⟶ X` be an étale morphism of schemes. Then `j` is flat, locally quasi-finite and
locally of finite presentation, so it carries the canonical weighting

`w(u) = length_{O_{U,u}}(O_{U,u} / m_{j(u)} O_{U,u}) · [κ(u) : κ(j(u))]_i`

of Stacks 0F3D, which is `AlgebraicGeometry.flatQuasiFiniteWeight`. This file computes that
weighting: it is the constant function `1`.

This is the computational content of Stacks 0GL4. The trace map `Tr_{f, w} : f_! f^{-1}K ⟶ K`
of Stacks 0GKG is characterised by its behaviour on stalks at a geometric point `ȳ`, where

`(f_! f^{-1}ℱ)_ȳ = ⨁_{f(x̄) = ȳ} ℱ_ȳ ⟶ ℱ_ȳ`

is multiplication by `w(x̄)` on the summand indexed by `x̄`. For an étale `j` the weighting is
`1`, so that map is the sum over the summands — which is exactly the counit of the adjunction
`j_! ⊣ j^{-1}`. The identification of Stacks 0GL4 is the statement proved here together with
the stalk characterisation of the trace, and is carried out in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.EtaleTraceIsCounit` as
`AlgebraicGeometry.hasWeightedTraceStalks_iff_eq_counit`.

## Main results

* `AlgebraicGeometry.flatQuasiFiniteWeight_eq_one_of_etale` — the canonical weighting of an
  étale morphism takes the value `1` at every point.
* `AlgebraicGeometry.flatQuasiFiniteWeight_etale_eq_one` — the same, as an equality of
  functions `U → ℤ`.
* `AlgebraicGeometry.separableDegreeWeightedFiberSum_flatQuasiFiniteWeight_of_etale` — the
  fibre integral `∫_{U → V} w` that defines the trace map of Stacks 0GKG, computed for an
  étale morphism with its canonical weighting: it is the plain separable-degree fibre count,
  the weights contributing nothing.

## Implementation notes

Both factors of the canonical weighting are computed separately, and each is one.

The local fibre ring `O_{U,u} / m_{j(u)} O_{U,u}` is the residue field `κ(u)`: an étale
morphism is formally unramified, so the maximal ideal of the base generates the maximal ideal
of the stalk. That is
`AlgebraicGeometry.map_maximalIdeal_eq_of_etale_fibers`. Its hypothesis —
that every fibre of `j` be étale over the residue field of its image — holds for an étale `j`
because étale morphisms are stable under base change. A quotient of a local ring by its maximal
ideal is a simple module, so it has length one.

The residue field extension `κ(u)/κ(j(u))` is separable, again by formal unramifiedness, so its
inseparable degree is one by `Algebra.IsSeparable.finInsepDegree_eq`.

The `Algebra (X.residueField (j u)) (U.residueField u)` instance used to read the inseparable
degree is the one `AlgebraicGeometry.flatQuasiFiniteWeight` itself uses, namely the algebra
attached to `Scheme.Hom.residueFieldMap`; it is introduced locally with `let` so that the
numerical claim can be stated, and matches the `let` in the definition up to definitional
equality.

## References

* [Stacks Project, Tag 0GL4](https://stacks.math.columbia.edu/tag/0GL4)
* [Stacks Project, Tag 0GKI](https://stacks.math.columbia.edu/tag/0GKI)
* [Stacks Project, Tag 0F3D](https://stacks.math.columbia.edu/tag/0F3D)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- Every fibre of an étale morphism is étale over the residue field of its image: the fibre
map is the second projection of a pullback of `j`, and étale morphisms are stable under base
change. -/
private theorem etale_fiberToSpecResidueField (s : X) :
    Etale (j.fiberToSpecResidueField s) := by
  dsimp only [Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiber]
  infer_instance

/-- **Stacks 0GL4.** The canonical weighting of Stacks 0F3D, for an étale morphism of schemes,
takes the value `1` at every point of the source.

This is the reason the trace map of Example 0GKI for an étale `j : U ⟶ X` is the counit of the
adjunction `j_! ⊣ j^{-1}`: the trace for a weighting `w` acts on the stalk
`(j_! j^{-1}ℱ)_ȳ = ⨁_{j(x̄) = ȳ} ℱ_ȳ` by multiplication by `w(x̄)` on the summand indexed by
`x̄`, so for `w = 1` it is the sum map, which is the counit. -/
@[stacks 0GL4 "The canonical weighting of Example 0GKI is identically 1 for an étale morphism —
the computation that makes its trace map the counit of `j_! ⊣ j^{-1}`. The remark's own equality
of the two morphisms is
`AlgebraicGeometry.hasWeightedTraceStalks_iff_eq_counit` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.EtaleTraceIsCounit`, which uses
this computation together with the stalk characterisation of Lemma 0GKG."]
theorem flatQuasiFiniteWeight_eq_one_of_etale (u : U) :
    flatQuasiFiniteWeight j u = 1 := by
  let _alg : Algebra (X.residueField (j u)) (U.residueField u) :=
    (j.residueFieldMap u).hom.toAlgebra
  have hlen : Module.length (U.presheaf.stalk u)
      ((U.presheaf.stalk u) ⧸ Ideal.map (j.stalkMap u).hom
        (maximalIdeal (X.presheaf.stalk (j u)))) = 1 := by
    rw [map_maximalIdeal_eq_of_etale_fibers j (etale_fiberToSpecResidueField j) u]
    have : IsSimpleModule (U.presheaf.stalk u)
        ((U.presheaf.stalk u) ⧸ maximalIdeal (U.presheaf.stalk u)) :=
      isSimpleModule_iff_isCoatom.mpr
        (Ideal.isMaximal_def.mp (maximalIdeal.isMaximal (U.presheaf.stalk u)))
    exact Module.length_eq_one _ _
  have := isSeparable_residueField_of_etale_fibers j (etale_fiberToSpecResidueField j) u
  show ((Module.length (U.presheaf.stalk u)
      ((U.presheaf.stalk u) ⧸ Ideal.map (j.stalkMap u).hom
        (maximalIdeal (X.presheaf.stalk (j u))))).toNat : ℤ) *
    (Field.finInsepDegree (X.residueField (j u)) (U.residueField u) : ℤ) = 1
  rw [hlen, Algebra.IsSeparable.finInsepDegree_eq]
  simp

/-- **Stacks 0GL4.** The canonical weighting of an étale morphism is the constant function
`1`, as an equality of functions `U → ℤ`. -/
@[stacks 0GL4 "The canonical weighting of Example 0GKI is identically 1 for an étale morphism,
as an equality of functions. Same scope as
`AlgebraicGeometry.flatQuasiFiniteWeight_eq_one_of_etale`; the remark's equality of the trace
with the counit is `AlgebraicGeometry.hasWeightedTraceStalks_iff_eq_counit`."]
theorem flatQuasiFiniteWeight_etale_eq_one : flatQuasiFiniteWeight j = 1 :=
  funext fun u => flatQuasiFiniteWeight_eq_one_of_etale j u

/-- **The fibre integral defining the trace map of Stacks 0GKG, for an étale morphism with its
canonical weighting.** The construction of `Tr_{f, w}` sends a section supported on a locally
closed `Z ⊂ X_V` finite over `V` to the fibre integral `∫_{Z → V} w|_Z`, which is
`AlgebraicGeometry.separableDegreeWeightedFiberSum`. For an étale morphism carrying its
canonical weighting that integral is the plain separable-degree fibre count: the weights
contribute nothing. -/
@[stacks 0GKG "The fibre integral `∫_{U → V} w` out of which the trace map `Tr_{f, w}` is
built, computed for an étale morphism with its canonical weighting: it is the plain
separable-degree fibre count. For an étale morphism with its canonical weighting the trace map
itself is the counit of `j_! ⊣ j^{-1}`, by
`AlgebraicGeometry.hasWeightedTraceStalks_iff_eq_counit` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.EtaleTraceIsCounit`; for a general
locally quasi-finite morphism and a general weighting its construction is a separate matter. Its
uniqueness and its characterisation on stalks are, for an arbitrary locally quasi-finite
morphism and an arbitrary integer-valued weight, in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceConstruction`; and the
fibre integral of a section supported on a part finite over the base, for an arbitrary locally
quasi-finite morphism and an arbitrary weighting, in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.FibreIntegral`."]
theorem separableDegreeWeightedFiberSum_flatQuasiFiniteWeight_of_etale
    {V : Scheme.{u}} (π : U ⟶ V) :
    separableDegreeWeightedFiberSum π (flatQuasiFiniteWeight j) =
      separableDegreeWeightedFiberSum π 1 := by
  rw [flatQuasiFiniteWeight_etale_eq_one]

end AlgebraicGeometry

end
