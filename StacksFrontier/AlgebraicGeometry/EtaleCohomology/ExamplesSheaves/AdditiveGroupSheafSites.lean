module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExamplesSheaves.AdditiveGroupSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.ChosenFlatSiteSheaves
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.ChosenSiteSheaves
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcSmallEtaleSheaf
import StacksCore.Tactic.StacksAttribute

/-!
# `Gₐ` on the seven sites of Stacks 03XB: Stacks 03P4, part (1)

Let `S` be a scheme. The sheaf `Gₐ` of [Stacks, Tag 03P4], part (1), is the abelian sheaf whose
sections over `T/S` are the global functions `Γ(T, 𝒪_T)` under addition. It is put here on each
of the seven sites `(Sch/S)_τ` and `S_τ` of [Stacks, Tag 03XB], for
`τ ∈ {fppf, syntomic, smooth, étale, Zariski}`. The sheaf condition is proved, not assumed.

Three of those sites, `(Sch/S)_{fppf}`, `(Sch/S)_{étale}` and `(Sch/S)_{Zar}`, already carry
`Gₐ` in `StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExamplesSheaves.AdditiveGroupSheaf`, as
`AlgebraicGeometry.BigFppfOver.additiveGroupSheaf` and its two companions. That file also builds
the general construction `Stacks.Sites.additiveGroupSheaf` on any site of schemes over `S` on
which global functions are a sheaf of types. Those four declarations are tagged with 03P4 below,
and nothing is restated.

The remaining four sites are the big syntomic and big smooth sites and the two small sites
`S_{étale}` and `S_{Zar}`. [Stacks, Tag 03XB] defines the small sites for `τ ∈ {étale, Zariski}`
only. `Gₐ` is a sheaf on each of these four sites for the same reason as on the first three:
global functions form an fpqc sheaf, and each site's canonical functor carries the fpqc sheaf
condition to it. This file does not compare their cohomology with that of the other sites. That
comparison is [Stacks, Tag 03P2].

## Main definitions

* `AlgebraicGeometry.BigSyntomicOver.additiveGroupSheaf`,
  `AlgebraicGeometry.BigSmoothOver.additiveGroupSheaf`,
  `AlgebraicGeometry.SmallEtale.additiveGroupSheaf`,
  `AlgebraicGeometry.SmallZariski.additiveGroupSheaf`: `Gₐ` on `(Sch/S)_{syntomic}`,
  `(Sch/S)_{smooth}`, `S_{étale}` and `S_{Zar}`.

## References

* [Stacks Project, Tag 03P4](https://stacks.math.columbia.edu/tag/03P4)
* [Stacks Project, Tag 03XB](https://stacks.math.columbia.edu/tag/03XB)
* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

universe u

add_to_stacks 03P4 "part (1), Gₐ on a site of schemes over S" Stacks.Sites.additiveGroupSheaf
add_to_stacks 03P4 "part (1), Gₐ on the big fppf site"
  AlgebraicGeometry.BigFppfOver.additiveGroupSheaf
add_to_stacks 03P4 "part (1), Gₐ on the big étale site"
  AlgebraicGeometry.BigEtaleOver.additiveGroupSheaf
add_to_stacks 03P4 "part (1), Gₐ on the big Zariski site"
  AlgebraicGeometry.BigZariskiOver.additiveGroupSheaf

namespace AlgebraicGeometry

variable (S : Scheme.{u})

namespace BigSyntomicOver

variable (B : BigSyntomicSite.{u}) (hS : B.Contains S)

/-- **Stacks 03P4, part (1), the big syntomic site.**  `Gₐ` as an abelian sheaf on
`(Sch/S)_{syntomic}`. -/
@[stacks 03P4 "part (1), Gₐ on the big syntomic site"]
noncomputable def additiveGroupSheaf : Sheaf (topology B S hS) AddCommGrpCat.{u} :=
  Stacks.Sites.additiveGroupSheaf S (Over.post (X := B.obj S hS) B.inclusion)
    (topology B S hS)
    (isSheaf_bigSyntomic_of_isSheaf_fpqc B S hS _
      (Stacks.Sites.isSheaf_fpqcOver_globalSections S))

end BigSyntomicOver

namespace BigSmoothOver

variable (B : BigSmoothSite.{u}) (hS : S.size < B.cutoff)

/-- **Stacks 03P4, part (1), the big smooth site.**  `Gₐ` as an abelian sheaf on
`(Sch/S)_{smooth}`. -/
@[stacks 03P4 "part (1), Gₐ on the big smooth site"]
noncomputable def additiveGroupSheaf : Sheaf (topology B S hS) AddCommGrpCat.{u} :=
  Stacks.Sites.additiveGroupSheaf S
    (Over.post (X := (⟨S, hS⟩ : B.category)) (ObjectProperty.ι _)) (topology B S hS)
    (isSheaf_bigSmooth_of_isSheaf_fpqc B S hS _
      (Stacks.Sites.isSheaf_fpqcOver_globalSections S))

end BigSmoothOver

namespace SmallEtale

variable (B : BigEtaleSite.{u}) (hS : B.Contains S)

/-- **Stacks 03P4, part (1), the small étale site.**  `Gₐ` as an abelian sheaf on
`S_{étale}`. -/
@[stacks 03P4 "part (1), Gₐ on the small étale site"]
noncomputable def additiveGroupSheaf : Sheaf (topology B S hS) AddCommGrpCat.{u} :=
  Stacks.Sites.additiveGroupSheaf S
    (inclusion B S hS ⋙ Over.post (X := B.obj S hS) B.inclusion) (topology B S hS)
    (isSheaf_chosenSmallEtale_of_isSheaf_fpqc B S hS _
      (Stacks.Sites.isSheaf_fpqcOver_globalSections S))

end SmallEtale

namespace SmallZariski

variable (B : BigZariskiSite.{u}) (hS : B.Contains S)

/-- **Stacks 03P4, part (1), the small Zariski site.**  `Gₐ` as an abelian sheaf on
`S_{Zar}`. -/
@[stacks 03P4 "part (1), Gₐ on the small Zariski site"]
noncomputable def additiveGroupSheaf : Sheaf (topology B S hS) AddCommGrpCat.{u} :=
  Stacks.Sites.additiveGroupSheaf S
    (inclusion B S hS ⋙ Over.post (X := (⟨S, hS⟩ : B.Schemes)) B.inclusion)
    (topology B S hS)
    (isSheaf_smallZariski_of_isSheaf_fpqc B S hS _
      (Stacks.Sites.isSheaf_fpqcOver_globalSections S))

end SmallZariski

end AlgebraicGeometry

end
