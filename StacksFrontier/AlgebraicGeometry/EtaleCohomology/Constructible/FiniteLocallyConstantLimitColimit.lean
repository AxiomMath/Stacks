module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimit.EssSurj
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimit.Fullness
import StacksCore.Tactic.StacksAttribute

/-!
# Finite locally constant sheaves on a limit of schemes form the colimit category

Let `X = lim X_i` be the limit of a directed inverse system of schemes with affine transition
morphisms, each `X_i` quasi-compact and quasi-separated. Stacks Tag 0GL2 asserts that the
category of finite locally constant sheaves (of sets, resp. of abelian groups) on `X_étale` is the
colimit of the corresponding categories on the `(X_i)_étale`, and that, for a Noetherian ring
`Λ`, the same holds for finite type locally constant sheaves of `Λ`-modules.

The colimit assertion is stated in the elementwise form
`AlgebraicGeometry.SmallEtaleStagesColimit`: the comparison is faithful and full (morphisms on
`X` between inverse images of sheaves at a stage are the filtered colimit of the morphisms at the
later stages, read through the canonical comparison of inverse images) and essentially
surjective. For a directed index this is exactly the statement that the canonical functor from
the filtered colimit of the categories is an equivalence.

Nothing is assumed beyond the source's hypotheses: the cone is a limit cone, the transition
morphisms are affine and the stages are quasi-compact and quasi-separated. Clause (3) is proved
for an arbitrary commutative ring `Λ`; the Noetherian hypothesis of the source is not needed.

The proof does not go through Tag 09YU. Locally on a stage a finite locally constant sheaf is
constant with finite (finitely generated) value; maps between such constant sheaves are locally
constant and therefore descend along the limit (`FiniteLocallyConstantLimit/Constants.lean`), and
étale gluing (`FiniteLocallyConstantLimit/Gluing.lean`) assembles the local pieces: morphisms in
`FiniteLocallyConstantLimit/Fullness.lean`, objects in `FiniteLocallyConstantLimit/EssSurj.lean`.

## Main results

* `AlgebraicGeometry.smallEtaleStagesColimit_isFiniteLocallyConstant_type` — clause (1).
* `AlgebraicGeometry.smallEtaleStagesColimit_isFiniteLocallyConstant_addCommGrpCat` — clause (2).
* `AlgebraicGeometry.smallEtaleStagesColimit_isFiniteTypeLocallyConstant_moduleCat` —
  clause (3).

## References

* [Stacks Project, Tag 0GL2](https://stacks.math.columbia.edu/tag/0GL2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance high] SmallEtale.hasWeakSheafify_over_moduleCat_site

attribute [local instance] SmallEtale.isRightAdjointPushforward_type
  SmallEtale.isRightAdjointPushforward_addCommGrpCat
  SmallEtale.isRightAdjointPushforward_moduleCat_site

variable (B : BigEtaleSite.{u}) {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

/-- **Stacks Tag 0GL2, clause (1).** Let `X = lim X_i` be the limit of a directed inverse system
of quasi-compact, quasi-separated schemes with affine transition morphisms. The category of
finite locally constant sheaves of sets on `X_étale` is the colimit of the categories of finite
locally constant sheaves of sets on the `(X_i)_étale`: the comparison is faithful, full and
essentially surjective. -/
@[stacks 0GL2 "part (1)"]
public theorem smallEtaleStagesColimit_isFiniteLocallyConstant_type (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesColimit B (Type (u + 1)) Dg c hX
      (isFiniteLocallyConstantSmallEtaleSheaf B (Type (u + 1))) where
  faithful := smallEtaleStagesFaithful_isFiniteLocallyConstant_type B Dg c hX hc haff hqc hqs
  full := smallEtaleStagesFull_isFiniteLocallyConstant_type B Dg c hX hc haff hqc hqs
  essSurj := smallEtaleStagesEssSurj_isFiniteLocallyConstant_type B Dg c hX hc haff hqc hqs

/-- **Stacks Tag 0GL2, clause (2).** Let `X = lim X_i` be the limit of a directed inverse system
of quasi-compact, quasi-separated schemes with affine transition morphisms. The category of
finite locally constant abelian sheaves on `X_étale` is the colimit of the categories of finite
locally constant abelian sheaves on the `(X_i)_étale`. -/
@[stacks 0GL2 "part (2)"]
public theorem smallEtaleStagesColimit_isFiniteLocallyConstant_addCommGrpCat (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesColimit B AddCommGrpCat.{u + 1} Dg c hX
      (isFiniteLocallyConstantSmallEtaleSheaf B AddCommGrpCat.{u + 1}) where
  faithful :=
    smallEtaleStagesFaithful_isFiniteLocallyConstant_addCommGrpCat B Dg c hX hc haff hqc hqs
  full := smallEtaleStagesFull_isFiniteLocallyConstant_addCommGrpCat B Dg c hX hc haff hqc hqs
  essSurj :=
    smallEtaleStagesEssSurj_isFiniteLocallyConstant_addCommGrpCat B Dg c hX hc haff hqc hqs

/-- **Stacks Tag 0GL2, clause (3).** Let `X = lim X_i` be the limit of a directed inverse system
of quasi-compact, quasi-separated schemes with affine transition morphisms and let `Λ` be a
commutative ring (the source assumes `Λ` Noetherian; that is not needed). The category of finite
type, locally constant sheaves of `Λ`-modules on `X_étale` is the colimit of the categories of
finite type, locally constant sheaves of `Λ`-modules on the `(X_i)_étale`. -/
@[stacks 0GL2 "part (3)"]
public theorem smallEtaleStagesColimit_isFiniteTypeLocallyConstant_moduleCat
    (Λ : Type (u + 1)) [CommRing Λ] (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesColimit B (ModuleCat.{u + 1} Λ) Dg c hX
      (isFiniteTypeLocallyConstantSmallEtaleSheaf B Λ) where
  faithful := smallEtaleStagesFaithful_isFiniteTypeLocallyConstant B Dg c hX Λ hc haff hqc hqs
  full := smallEtaleStagesFull_isFiniteTypeLocallyConstant B Dg c hX Λ hc haff hqc hqs
  essSurj :=
    smallEtaleStagesEssSurj_isFiniteTypeLocallyConstant_moduleCat B Dg c hX Λ hc haff hqc hqs

end AlgebraicGeometry

end
