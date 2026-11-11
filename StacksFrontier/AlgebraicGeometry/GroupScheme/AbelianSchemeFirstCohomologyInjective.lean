module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianSchemeTorsorTrivialOfGenericSection
public import StacksFrontier.AlgebraicGeometry.GroupScheme.ProperRationalSectionExtension
public import StacksFrontier.AlgebraicGeometry.GroupScheme.TorsorEtaleLocalSection

/-!
# Injectivity of first fppf cohomology of an abelian scheme at the generic point

Let `W` be a two dimensional regular integral Noetherian scheme with function field `K` and let
`G → W` be an abelian scheme. Every fppf `G`-torsor with a section over `Spec K` is trivial, and
consequently the restriction map `H¹_fppf(W, G) → H¹_fppf(Spec K, G)` is injective.

## Main results

* `AlgebraicGeometry.isTrivial_of_nonempty_sections_genericPoint`: an fppf `G`-torsor with a
  section over `Spec K` is trivial.
* `AlgebraicGeometry.fppfH1_restriction_genericPoint_injective_of_dim_two`: **Stacks 0AF9**.

Together with Stacks 0AFA (`AlgebraicGeometry.Space.fppfH1_isAddTorsion`) it shows that the first
fppf cohomology classes over the completion of the triangle are torsion, the last input of
Stacks 0CXX (`Deformation.Artin.exists_nonEffectiveSystem_quotientStack_abelianVariety`).

## Implementation notes

The source's sketch closes a generic section of the torsor `P`, resolves its indeterminacy by
blowups in closed points and contracts the exceptional curves, which map constantly to `P`
because there are no nonconstant morphisms from the projective line to a group scheme
(Tag 0AEN). Here the same argument is run on the group scheme rather than on the torsor:

1. `P` is trivial étale locally on `W`
   (`AlgebraicGeometry.exists_etale_section_of_torsor`), since it is an algebraic space smooth
   over `W` and smooth morphisms have sections étale locally (Tag 055U); the abelian scheme is
   smooth by `AlgebraicGeometry.smooth_of_isAbelianScheme`.
2. Over an integral étale `V → W`, which is again regular, Noetherian and of dimension at most
   two, the difference of the generic section and a trivialising section is a rational section
   of the proper group scheme `G_V`, which extends to a section
   (`AlgebraicGeometry.GroupScheme.exists_section_extending_of_isRegular`): this is where the
   resolution by blowups in closed points (Tag 0C5H), the contraction of exceptional curves
   (Tag 0C5J) and the rigidity of the projective line
   (`AlgebraicGeometry.exists_section_eq_comp_of_projectiveLineProj`, the scheme form of
   Tag 0AEN) enter.
3. The local sections extending the generic one agree on overlaps, because the overlaps are
   reduced and flat over `W`, and glue to a section of `P` over `W`
   (`AlgebraicGeometry.isTrivial_of_nonempty_genericPoint_of_extend_of_local`).

The passage from torsors to first cohomology is
`AlgebraicGeometry.fppfH1_restriction_genericPoint_injective`.

## References

* [Stacks Project, Tag 0AF9](https://stacks.math.columbia.edu/tag/0AF9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (W : Scheme.{u}) (hW : B.Contains W)

/-- **An fppf torsor under an abelian scheme over a two dimensional regular integral Noetherian
scheme with a section over the generic point is trivial.** -/
public theorem isTrivial_of_nonempty_sections_genericPoint
    [IsIntegral W] [AlgebraicGeometry.IsNoetherian W] (hreg : IsRegular W)
    (hdim : topologicalKrullDim (W : Type u) = (2 : WithBot ℕ∞))
    (hK : B.Contains (Spec W.functionField))
    (G : Over W) [GrpObj G] [IsAbelianScheme G] (hG : B.Contains G.left)
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (pointsSheaf B W hW G hG))
    (hne : Nonempty (F.1.presheaf.obj (op (genericPointObj B W hW hK)))) :
    F.1.IsTrivial :=
  isTrivial_of_nonempty_genericPoint_of_extend_of_local B W hW hreg hdim.le hK G hG
    (fun X _ _ hX hXdim H _ _ σ hσ =>
      GroupScheme.exists_section_extending_of_isRegular X hX hXdim H σ hσ)
    (fun G' _ _ _ hG' F' w => exists_etale_section_of_torsor B W hW G' hG' F' w) F hne

/-- **Stacks 0AF9.** Let `W` be a two dimensional regular integral Noetherian scheme with
function field `K` and let `G → W` be an abelian scheme. Then the restriction map
`H¹_fppf(W, G) → H¹_fppf(Spec K, G)` along the generic point is injective.

A class in the kernel is the class of a torsor with a section over `Spec K`, which is trivial by
`AlgebraicGeometry.isTrivial_of_nonempty_sections_genericPoint`. -/
@[stacks 0AF9]
public theorem fppfH1_restriction_genericPoint_injective_of_dim_two
    [IsIntegral W] [AlgebraicGeometry.IsNoetherian W] (hreg : IsRegular W)
    (hdim : topologicalKrullDim (W : Type u) = (2 : WithBot ℕ∞))
    (hK : B.Contains (Spec W.functionField))
    (G : Over W) [GrpObj G] [IsAbelianScheme G] (hG : B.Contains G.left)
    [HasSheafify (BigFppfOver.topology B W hW) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (BigFppfOver.topology B W hW) AddCommGrpCat.{u})] :
    Function.Injective (((pointsSheaf B W hW G hG).cohomologyPresheaf 1).map
      (genericPointToBase B W hW hK).op) :=
  fppfH1_restriction_genericPoint_injective B W hW hreg hdim hK G hG
    (isTrivial_of_nonempty_sections_genericPoint B W hW hreg hdim hK G hG)

end AlgebraicGeometry

end
