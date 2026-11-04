module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.UnibranchContinuousModules
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TopologicalInvarianceFundamental.UniversalHomeomorphismEquivalence

/-!
# Finite étale covers of the normalization of a geometrically unibranch scheme

Let `X` be an irreducible, geometrically unibranch scheme and let `ν : X^ν → X` be its
normalization. By Stacks Tag 0GIQ the morphism `ν` is a universal homeomorphism, and by
Stacks Tag 0BQN base change along a universal homeomorphism is an equivalence `FÉt_X ⥤ FÉt_{X^ν}`.
Both inputs are available unconditionally, so the equivalence at `ν` is available
unconditionally; this module records it and feeds it to the reduction of Tag 0GIY.

## Main results

* `AlgebraicGeometry.Scheme.connectedSpace_normalizationSchemeOfIrreducible` — the normalization
  of an irreducible geometrically unibranch scheme is connected, being homeomorphic to the
  scheme itself.
* `AlgebraicGeometry.finiteEtaleBaseChange_normalizationOfIrreducible_isEquivalence` — base
  change along the normalization of an irreducible geometrically unibranch scheme is an
  equivalence of categories of finite étale covers.
* `AlgebraicGeometry.finiteTypeLocallyConstantEquivContinuousModuleOfNormalization` — the
  reduction of Tag 0GIY along the normalization, with its finite étale input discharged.

## Implementation notes

`AlgebraicGeometry.finiteEtaleBaseChange_isEquivalence_of_universalHomeomorphism` is the full
equivalence of Tag 0BQN — faithfulness, fullness and essential surjectivity together — proved
for an arbitrary universal homeomorphism by transporting the equivalence of small étale sites of
Tag 04DZ across the finiteness criterion
`AlgebraicGeometry.isFinite_of_isFinite_pullback_snd_of_universalHomeomorphism`. No part of
Tag 0BQN is reproved here: the only content of
`AlgebraicGeometry.finiteEtaleBaseChange_normalizationOfIrreducible_isEquivalence` is that the
normalization of an irreducible geometrically unibranch scheme satisfies the hypothesis of that
theorem, which is Tag 0GIQ.

`AlgebraicGeometry.finiteTypeLocallyConstantEquivContinuousModuleOfNormalization` is
`AlgebraicGeometry.finiteTypeLocallyConstantEquivContinuousModule` with its instance argument on
the finite étale covers of the normalization supplied. Its remaining inputs are the equivalence of
the finite type locally constant module categories along a universal homeomorphism (Tag 04DZ at
the level of module sheaves, `hinvariance`), a lift `xν` of the geometric point to the
normalization, and Tag 0GIY itself for an integral normal scheme (`hnormal`). The last of these is
the bulk of the source's proof and rests on Tags 0BQM, 0BTD, 0BQI, 03RV, 0245 and 03QW.

The connectedness of the normalization stays an instance argument because
`AlgebraicGeometry.EtaleFundamentalGroup` needs it to be in scope already for the type of
`hnormal` to be written down, so it cannot be discharged inside the proof. It is no obligation on
a caller: `AlgebraicGeometry.Scheme.connectedSpace_normalizationSchemeOfIrreducible` supplies it
from the same irreducibility and geometric unibranchness the statement already assumes.

## References

* [Stacks Project, Tag 0BQN](https://stacks.math.columbia.edu/tag/0BQN)
* [Stacks Project, Tag 0GIQ](https://stacks.math.columbia.edu/tag/0GIQ)
* [Stacks Project, Tag 0GIY](https://stacks.math.columbia.edu/tag/0GIY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open Stacks.ConstantSheaf Stacks.GroupCohomology

universe u w r

namespace AlgebraicGeometry

/-- The normalization of an irreducible, geometrically unibranch scheme is connected: the
normalization morphism is a universal homeomorphism by Stacks Tag 0GIQ, hence a homeomorphism,
and an irreducible space is connected. -/
theorem Scheme.connectedSpace_normalizationSchemeOfIrreducible (X : Scheme.{u})
    [IrreducibleSpace X] (hX : IsGeometricallyUnibranch X) :
    ConnectedSpace (Scheme.normalizationSchemeOfIrreducible X) :=
  (IsHomeomorph.homeomorph _
    ((Scheme.universalHomeomorphism_normalization X hX).universally_isHomeomorph
      _ _ _ IsPullback.of_id_snd)).connectedSpace_iff.mpr inferInstance

/-- **Stacks Project, Tag 0BQN at the normalization of a geometrically unibranch scheme.** Let
`X` be an irreducible, geometrically unibranch scheme. Base change along the normalization
`ν : X^ν → X` is an equivalence `FÉt_X ⥤ FÉt_{X^ν}`, `V ↦ V ×_X X^ν`.

The normalization of an irreducible geometrically unibranch scheme is a universal homeomorphism
by Stacks Tag 0GIQ, and base change along a universal homeomorphism is an equivalence of
categories of finite étale covers by
`AlgebraicGeometry.finiteEtaleBaseChange_isEquivalence_of_universalHomeomorphism`. -/
@[stacks 0BQN "fullness and essential surjectivity of the base change functor `FÉt_X ⥤ FÉt_Xᵛ`, \
alongside faithfulness, i.e. the whole equivalence, specialised to the normalization of an \
irreducible geometrically unibranch scheme. No part of Tag 0BQN is reproved here. All three \
halves are already available for an arbitrary universal homeomorphism, unconditionally, as \
`AlgebraicGeometry.finiteEtaleBaseChange_isEquivalence_of_universalHomeomorphism`, which also \
carries this tag, and whose faithfulness half is additionally isolated as \
`AlgebraicGeometry.faithful_finiteEtaleBaseChange_of_universalHomeomorphism`. What this \
declaration adds is only that the normalization morphism of an irreducible geometrically \
unibranch scheme is such a universal homeomorphism, which is Tag 0GIQ, so that the equivalence \
becomes available at the morphism along which the source reduces Tag 0GIY"]
theorem finiteEtaleBaseChange_normalizationOfIrreducible_isEquivalence (X : Scheme.{u})
    [IrreducibleSpace X] (hX : IsGeometricallyUnibranch X) :
    (finiteEtaleBaseChange (Scheme.normalizationOfIrreducible X)).IsEquivalence :=
  have : UniversalHomeomorphism (Scheme.normalizationOfIrreducible X) :=
    Scheme.universalHomeomorphism_normalization X hX
  finiteEtaleBaseChange_isEquivalence_of_universalHomeomorphism _

/-- **The reduction of Stacks Project, Tag 0GIY along the normalization, with its finite étale
input discharged.** Let `X` be an irreducible, geometrically unibranch scheme in a big étale
site, let `x` be a geometric point of `X` and let `Λ` be a ring. Suppose given an equivalence
`hinvariance` of the finite type locally constant `Λ`-module categories of `X` and of its
normalization `X^ν`, induced by the universal homeomorphism `ν`; a lift `xν` of `x` to `X^ν`;
and the tag for `X^ν`, which is an integral normal scheme. Then the finite type locally constant
sheaves of `Λ`-modules on `X_étale` are equivalent to the finite `Λ`-modules with a continuous
`π₁(X, x)`-action.

This is `AlgebraicGeometry.finiteTypeLocallyConstantEquivContinuousModule` with its instance
argument on the finite étale covers of `X^ν` supplied, by
`AlgebraicGeometry.finiteEtaleBaseChange_normalizationOfIrreducible_isEquivalence`. The
connectedness of `X^ν` is
`AlgebraicGeometry.Scheme.connectedSpace_normalizationSchemeOfIrreducible` and remains an instance
argument only because the type of `hnormal` mentions `π₁(X^ν, xν)`. -/
def finiteTypeLocallyConstantEquivContinuousModuleOfNormalization
    (B : BigEtaleSite.{u}) (X : B.Scheme) [IrreducibleSpace X.obj]
    (hX : IsGeometricallyUnibranch X.obj) (x : GeometricPoint X.obj)
    (Λ : Type r) [Ring Λ]
    [∀ V : SmallEtale B X.obj X.property,
      HasWeakSheafify ((SmallEtale.topology B X.obj X.property).over V) (ModuleCat.{w} Λ)]
    (hν : B.Contains (Scheme.normalizationSchemeOfIrreducible X.obj))
    [ConnectedSpace (Scheme.normalizationSchemeOfIrreducible X.obj)]
    [∀ V : SmallEtale B (Scheme.normalizationSchemeOfIrreducible X.obj) hν,
      HasWeakSheafify
        ((SmallEtale.topology B (Scheme.normalizationSchemeOfIrreducible X.obj) hν).over V)
        (ModuleCat.{w} Λ)]
    (xν : GeometricPoint (Scheme.normalizationSchemeOfIrreducible X.obj))
    (hx : xν.map (Scheme.normalizationOfIrreducible X.obj) = x)
    (hinvariance : UniversalHomeomorphism (Scheme.normalizationOfIrreducible X.obj) →
      (FiniteTypeLocallyConstantModuleCategory Λ (SmallEtale.topology B X.obj X.property) ≌
        FiniteTypeLocallyConstantModuleCategory Λ
          (SmallEtale.topology B (Scheme.normalizationSchemeOfIrreducible X.obj) hν)))
    (hnormal : FiniteTypeLocallyConstantModuleCategory Λ
        (SmallEtale.topology B (Scheme.normalizationSchemeOfIrreducible X.obj) hν) ≌
      FiniteTypeContinuousModule Λ
        (EtaleFundamentalGroup (Scheme.normalizationSchemeOfIrreducible X.obj) xν)) :
    FiniteTypeLocallyConstantModuleCategory Λ (SmallEtale.topology B X.obj X.property) ≌
      FiniteTypeContinuousModule Λ (EtaleFundamentalGroup X.obj x) :=
  let := finiteEtaleBaseChange_normalizationOfIrreducible_isEquivalence X.obj hX
  finiteTypeLocallyConstantEquivContinuousModule B X hX x Λ hν xν hx hinvariance hnormal

end AlgebraicGeometry

end
