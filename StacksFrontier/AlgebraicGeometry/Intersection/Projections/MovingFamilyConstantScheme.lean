module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyConstant
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Product
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.FiniteProjection

/-!
# Clause (2) of Tag 0B1T for the constant family, scheme theoretically

Clause (2) of Tag 0B1T asks for `C'_0 = C` **scheme theoretically**: an equality of closed
subschemes of `𝐏^N`, not merely of their underlying sets. For the constant family
`C' = C × 𝐏^1` this file proves it.

The fibre of a closed subscheme of `𝐏(W) ×_k 𝐏(V)` over a closed point `λ` of `𝐏(W)` is the
pullback of its ideal sheaf along the section `σ_λ` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilySection`, and the constant
family carries the reduced structure `vanishingIdeal (pr₂⁻¹ X)`. Two steps:

* the reduced structure on the constant family is the pullback of the reduced structure on `X`,
  because `𝐏(W) ×_k X` is a variety over an algebraically closed field and hence reduced;
* pulling that back along `σ_λ` gives the reduced structure on `X` itself, because `σ_λ` is a
  section of `pr₂` and `comap` is functorial.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.comap_vanishingIdeal_lineProductPoint`: the reduced
  closed subscheme on the constant family is the scheme-theoretic preimage of the reduced closed
  subscheme on `X`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.comap_vanishingIdeal_lineProductConstant`:
  **clause (2) of Tag 0B1T for the constant family, scheme theoretically** — the
  scheme-theoretic fibre of `X × 𝐏(W)` over every closed point of `𝐏(W)` is `X`.

## Implementation notes

**Where the two statements are used.** Tag 0B1T's family is the constant one exactly when
nothing has to be moved (`C = 𝐏^N`, or `C ∩ X = ∅`), in
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_movingFamily_of_subvariety_fixed` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingLemmaFixedPoints`. For the
general-position construction — the image of the graph of the family of projective
transformations — the scheme-theoretic form of clause (2) rests on a different fact, that the
family is an isomorphism over a neighbourhood of `0`, and is
`AlgebraicGeometry.ProjectiveSpaceOfModule.comap_vanishingIdeal_lineProductSection_of_translate`
of `StacksFrontier.AlgebraicGeometry.Intersection.Projections.LocalTranslationFamily`, which itself
uses `comap_vanishingIdeal_lineProductPoint` of this file.

**Why reducedness of `𝐏(W) ×_k X` is the content.** An ideal sheaf whose support is `T` is
contained in `vanishingIdeal T`, so the inclusion of the reduced closed subscheme on the fibre
into the scheme-theoretic fibre is automatic from the equality of the underlying sets; the
reverse inclusion is exactly radicality of the pulled-back ideal sheaf, which is
`AlgebraicGeometry.Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme` and needs the
scheme-theoretic preimage to be reduced. Here it is reduced because
`AlgebraicGeometry.ProjectiveSpaceOfModule.lineProductConstantIso` identifies it with the
product `𝐏(W) ×_k X` of two varieties, which over an algebraically closed field is again a
variety by `AlgebraicGeometry.isVariety_pullback` (Tag 0AZM) and so integral, hence reduced.
Irreducibility of `X` is therefore used, although the conclusion does not mention it: the
product of two *reduced* schemes over an algebraically closed field is reduced as well, but it
is the variety form of the product theorem that the library carries.

## References

* [Stacks Project, Tag 0B1T](https://stacks.math.columbia.edu/tag/0B1T)
* [Stacks Project, Tag 0AZM](https://stacks.math.columbia.edu/tag/0AZM)
* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [Nontrivial V]
  (W : Type u) [AddCommGroup W] [Module k W] [FiniteDimensional k W] [Nontrivial W]

/-- **A projective space over an algebraically closed field is a variety.** It is irreducible and
reduced, hence integral, and its structure morphism is proper, hence separated, of finite type
and quasi-compact. -/
public instance isVariety_projectiveSpaceOfModuleToSpec :
    IsVariety k (projectiveSpaceOfModuleToSpec k V) := by
  have := isProper_projectiveSpaceOfModuleToSpec k V
  have : IsReduced (projectiveSpaceOfModule k V) := isReduced_projectiveSpaceOfModule k V
  have : IsIntegral (projectiveSpaceOfModule k V) :=
    isIntegral_of_irreducibleSpace_of_isReduced _
  constructor

omit [IsAlgClosed k] in
/-- **A closed subvariety of `𝐏(V)`, with its reduced structure, is a variety.** It is
irreducible because the subset is, reduced because the structure is the reduced one, and its
structure morphism is proper, being a closed immersion followed by the proper structure morphism
of `𝐏(V)`. -/
public theorem isVariety_closedSubschemeOfToSpec
    (X : Set (projectiveSpaceOfModule k V)) (hX : IsClosed X) (hXirr : IsIrreducible X) :
    IsVariety k (closedSubschemeOfToSpec k V X hX) := by
  have := isProper_projectiveSpaceOfModuleToSpec k V
  have : IsProper (closedSubschemeOfToSpec k V X hX) := by
    rw [closedSubschemeOfToSpec]
    infer_instance
  have : IrreducibleSpace (closedSubschemeOf k V X hX) :=
    irreducibleSpace_vanishingIdeal_subscheme X hX hXirr
  have : IsReduced (closedSubschemeOf k V X hX) :=
    inferInstanceAs (IsReduced (Scheme.IdealSheafData.vanishingIdeal
      (⟨X, hX⟩ : Closeds (projectiveSpaceOfModule k V))).subscheme)
  have : IsIntegral (closedSubschemeOf k V X hX) :=
    isIntegral_of_irreducibleSpace_of_isReduced _
  constructor

/-- **The product `𝐏(W) ×_k X` of a projective space with a closed subvariety is reduced**, being
a product of two varieties over an algebraically closed field and so a variety itself, by Tag
0AZM. -/
public theorem isReduced_lineProductConstantProd
    (X : Set (projectiveSpaceOfModule k V)) (hX : IsClosed X) (hXirr : IsIrreducible X) :
    IsReduced (lineProductConstantProd k V W X hX) := by
  have := isVariety_closedSubschemeOfToSpec k V X hX hXirr
  have := isVariety_pullback k (projectiveSpaceOfModuleToSpec k W)
    (closedSubschemeOfToSpec k V X hX)
  infer_instance

/-- **The reduced closed subscheme on the constant family is the scheme-theoretic preimage of the
reduced closed subscheme on `X`.** The preimage has the constant family as its support, by
`AlgebraicGeometry.Scheme.IdealSheafData.support_comap`, and it is reduced because it is
isomorphic to the product `𝐏(W) ×_k X`. -/
public theorem comap_vanishingIdeal_lineProductPoint
    (X : Set (projectiveSpaceOfModule k V)) (hX : IsClosed X) (hXirr : IsIrreducible X) :
    (Scheme.IdealSheafData.vanishingIdeal
          (⟨X, hX⟩ : Closeds (projectiveSpaceOfModule k V))).comap (lineProductPoint k V W) =
      Scheme.IdealSheafData.vanishingIdeal
        (⟨lineProductConstant k V W X, isClosed_lineProductConstant k V W X hX⟩ :
          Closeds (lineProduct k V W)) := by
  have := isReduced_lineProductConstantProd k V W X hX hXirr
  have : IsReduced ((Scheme.IdealSheafData.vanishingIdeal
      (⟨X, hX⟩ : Closeds (projectiveSpaceOfModule k V))).comap
        (lineProductPoint k V W)).subscheme :=
    ObjectProperty.prop_of_iso IsReduced
      ((Scheme.IdealSheafData.vanishingIdeal
        (⟨X, hX⟩ : Closeds (projectiveSpaceOfModule k V))).comapIso
          (lineProductPoint k V W) ≪≫ lineProductConstantIso k V W X hX).symm inferInstance
  refine Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ ?_
  refine Closeds.ext ?_
  rw [Scheme.IdealSheafData.support_comap]
  change (lineProductPoint k V W).base ⁻¹'
      ((Scheme.IdealSheafData.vanishingIdeal
        (⟨X, hX⟩ : Closeds (projectiveSpaceOfModule k V))).support :
          Set (projectiveSpaceOfModule k V)) =
      lineProductConstant k V W X
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- **Clause (2) of Tag 0B1T for the constant family, scheme theoretically.** The
scheme-theoretic fibre of the constant family `X × 𝐏(W)` over every closed point of `𝐏(W)` is
the reduced closed subscheme on `X` itself: the reduced structure on the constant family is the
preimage of the reduced structure on `X` under the projection to `𝐏(V)`, and the section at a
closed point of `𝐏(W)` is a section of that projection, so the two pullbacks compose to the
identity. -/
public theorem comap_vanishingIdeal_lineProductConstant
    (X : Set (projectiveSpaceOfModule k V)) (hX : IsClosed X) (hXirr : IsIrreducible X)
    (lam : projectiveSpaceOfModule k W) (hlam : IsClosed ({lam} : Set _)) :
    (Scheme.IdealSheafData.vanishingIdeal
          (⟨lineProductConstant k V W X, isClosed_lineProductConstant k V W X hX⟩ :
            Closeds (lineProduct k V W))).comap (lineProductSection k V W lam hlam) =
      Scheme.IdealSheafData.vanishingIdeal
        (⟨X, hX⟩ : Closeds (projectiveSpaceOfModule k V)) := by
  rw [← comap_vanishingIdeal_lineProductPoint k V W X hX hXirr,
    ← Scheme.IdealSheafData.comap_comp, lineProductSection_comp_lineProductPoint,
    Scheme.IdealSheafData.comap_id]

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
