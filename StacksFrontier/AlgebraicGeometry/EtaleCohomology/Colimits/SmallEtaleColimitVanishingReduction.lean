module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.OpensAcyclicityTransport
import all StacksFrontier.CategoryTheory.Sites.InverseSystem.CohomologyOfColimitOfFiniteSites

/-!
# The vanishing hypothesis of Stacks 09YQ, discharged into geometry

In the namespace `Stacks.EtaleCohomology.SmallEtaleLimitCohomology`, the theorem
`isCohomologyColimit_of_degreeZero_of_vanishing_of_injectiveEmbeddings` is the dimension shift of
[Stacks, Tag 09YQ] on Mathlib's small étale sites with its dévissage hypothesis discharged. Three
hypotheses remain there: the degree-zero statement `H0`, the *vanishing* statement `HV` — that
`H^q(X, colim f_i^{-1}G_i)` vanishes for `q > 0` whenever every `G_i` is injective — and
[Stacks, Tag 0EXZ] levelwise.

`HV` is an `Ext` statement about the sheaf on the limit. This file replaces it, for every presented
system at once, by the two hypotheses of
`OpensAcyclicity.subsingleton_H_smallEtale_of_affineOpens_acyclic_of_sectionsDifference`:
acyclicity of the *restriction* of the colimit sheaf to each affine open of the limit, and a
condition on its *sections* over the pairwise intersections. Both are statements about the small
étale site of a scheme and about sections of a sheaf on it.

## Main results

* `isCohomologyColimit_of_degreeZero_of_affineOpensAcyclic`: the colimit statement of
  [Stacks, Tag 09YQ] in every degree, from the degree-zero statement, the two geometric statements
  above, and the levelwise [Stacks, Tag 0EXZ].

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EXZ](https://stacks.math.columbia.edu/tag/0EXZ)
* [Stacks Project, Tag 0A50](https://stacks.math.columbia.edu/tag/0A50)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.EtaleCohomology.OpensAcyclicity (SectionsDifference smallEtaleOpensRestrict)

universe v u

namespace Stacks.EtaleCohomology.SmallEtaleLimitCohomology

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}}
  [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}]
  [∀ i : Iᵒᵖ, HasExt.{u + 1} (Sheaf (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1})]
  {c : Cone D} [HasSheafify (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})]

/-- **The colimit statement of [Stacks, Tag 09YQ] in every degree, with the vanishing hypothesis
read as two statements of geometry.** Let `I` be a directed set, let `D` be an inverse system of
schemes over `I`, let `c` be a limit cone with quasi-compact quasi-separated vertex `X`, and
assume

* `H0`, the degree-zero statement for every system of abelian sheaves on the small étale sites of
  the levels presenting its colimit on the small étale site of `X`;
* `haff`: for such a system that is *pointwise injective*, the restriction of its sheaf on `X` to
  the small étale site of each affine open of `X` has vanishing global cohomology in every
  positive degree;
* `hsub`: for such a system, every section of its sheaf on `X` over `U ⊓ V`, with `U` a
  quasi-compact open and `V` an affine open, is the difference of a section over `U` and a section
  over `V`;
* `H0EXZ`, [Stacks, Tag 0EXZ] for systems of abelian sheaves on these sites.

Then the statement of Stacks 09YQ holds in every degree `p`.

This is `isCohomologyColimit_of_degreeZero_of_vanishing_of_injectiveEmbeddings` with its
hypothesis `HV` supplied by
`OpensAcyclicity.subsingleton_H_smallEtale_of_affineOpens_acyclic_of_sectionsDifference`; the
hypotheses `haff` and `hsub` together say exactly what `HV` says. -/
theorem isCohomologyColimit_of_degreeZero_of_affineOpensAcyclic
    [IsDirected I (· ≤ ·)] [Nonempty I] [UnivLE.{v, u + 1}]
    [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
    (H0 : ∀ E : PresentedSystem (c := c) IsColimitPresentation, IsCohomologyColimit E 0)
    (haff : ∀ E : PresentedSystem (c := c) IsColimitPresentation,
      (∀ i : Iᵒᵖ, Injective (E.sys.obj i)) →
      ∀ V : c.pt.Opens, IsAffineOpen V → ∀ n, 0 < n →
        Subsingleton (Sheaf.H.{u + 1} ((smallEtaleOpensRestrict c.pt V).obj E.sheaf) n))
    (hsub : ∀ E : PresentedSystem (c := c) IsColimitPresentation,
      (∀ i : Iᵒᵖ, Injective (E.sys.obj i)) →
      ∀ U V : c.pt.Opens, IsCompact (U : Set c.pt) → IsAffineOpen V →
        SectionsDifference ((MayerVietoris.mayerVietorisRestrict c.pt).obj E.sheaf) U V)
    (H0EXZ : HasPointwiseInjectiveEmbeddings D) (p : ℕ)
    (E : PresentedSystem (c := c) IsColimitPresentation) : IsCohomologyColimit E p :=
  isCohomologyColimit_of_degreeZero_of_vanishing_of_injectiveEmbeddings H0
    (fun E' hinj q hq =>
      OpensAcyclicity.subsingleton_H_smallEtale_of_affineOpens_acyclic_of_sectionsDifference
        E'.sheaf (haff E' hinj) (hsub E' hinj) q hq)
    H0EXZ p E

end Stacks.EtaleCohomology.SmallEtaleLimitCohomology

end
