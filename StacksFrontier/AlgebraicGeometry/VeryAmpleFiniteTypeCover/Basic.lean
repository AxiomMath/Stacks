module

public import StacksFrontier.AlgebraicGeometry.VeryAmpleAffineBase.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks Tag 02NQ: relative very ampleness read on a covering of the base

Stacks Tag 02NQ (Morphisms of Schemes, "Ample and very ample sheaves relative to finite type
morphisms") says that for a morphism of schemes `f : X ⟶ S` of finite type and an invertible
`𝒪_X`-module `L` the following are equivalent:

1. `L` is `f`-relatively very ample, and
2. there are an open covering `S = ⋃ V_j`, for each `j` an integer `n_j`, and immersions
   `i_j : X_j = f⁻¹(V_j) ⟶ 𝐏^{n_j}_{V_j}` over `V_j` with `L|_{X_j} ≅ i_j^* 𝒪(1)`.

Condition (1) is `Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple`, Stacks Tag 01VM, which names
both `𝐏(E)` and `𝒪_{𝐏(E)}(1)`. Condition (2) is
`Stacks.VeryAmpleFiniteTypeCover.HasProjectiveImmersionCover`, assembled from
`Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver` at the restricted morphisms `f ∣_ V_j`,
whose source is `f⁻¹(V_j)`.

This file defines condition (2); the equivalence is proved in
`StacksFrontier.AlgebraicGeometry.VeryAmpleFiniteTypeCover.Equivalence`.

## Main definitions

* `Stacks.VeryAmpleFiniteTypeCover.HasProjectiveImmersionCover`: condition (2) of Stacks Tag 02NQ.
* `Stacks.VeryAmpleFiniteTypeCover.VeryAmpleOfProjectiveImmersion`: the statement of Stacks Tag
  01VT, (5) implies (3) — an immersion into `𝐏^n_S` over `S` carrying `𝒪(1)` to `L` exhibits `L` as
  relatively very ample.

## Main results

* `Stacks.VeryAmpleFiniteTypeCover.hasProjectiveImmersionCover_of_forall`: condition (2) from its
  pointwise form, a neighbourhood of each point of the base rather than an indexed covering.

## Implementation notes

The restriction of `L` is spelled with `RingedSpaceModuleAdjunction.modulePullback`, as in
`Stacks.RelativeAmple.IsRelativelyAmple`, rather than with
`AlgebraicGeometry.Scheme.Modules.pullback`: the former carries the invertibility instance
`Stacks.InvertiblePullback.isInvertibleModule_restrict`. The covering is an indexed family with
`(⨆ j, V j) = ⊤`, transcribing the source's `S = ⋃ V_j` with `n_j` depending on `j`; the degree
`n_j` is existentially quantified inside `Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver`.
Finite type is `LocallyOfFiniteType` together with `QuasiCompact`.

`Stacks.VeryAmpleFiniteTypeCover.HasProjectiveImmersionCover` differs from
`Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmpleLocallyOnBase`, clause (2) of Tag 01VR: the latter
asks over each member for an immersion into the projective bundle `𝐏(E_j)` of an arbitrary
quasi-coherent module, the former for an immersion into the finite-dimensional projective space
`𝐏^{n_j}_{V_j}`.

## References

* [Stacks Project, Tag 02NQ](https://stacks.math.columbia.edu/tag/02NQ)
* [Stacks Project, Tag 02NP](https://stacks.math.columbia.edu/tag/02NP)
* [Stacks Project, Tag 01VR](https://stacks.math.columbia.edu/tag/01VR)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 01VT](https://stacks.math.columbia.edu/tag/01VT)
* [Stacks Project, Tag 0B3F](https://stacks.math.columbia.edu/tag/0B3F)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Ample
open Stacks.AmpleProjectiveImmersion

universe u

namespace Stacks.VeryAmpleFiniteTypeCover

/-! ### Condition (2) of Stacks Tag 02NQ -/

/-- **Condition (2) of Stacks Tag 02NQ.** There are an open covering `S = ⋃ V_j`, for each `j` an
integer `n_j`, and immersions `i_j : X_j = f⁻¹(V_j) ⟶ 𝐏^{n_j}_{V_j}` over `V_j` such that
`L|_{X_j} ≅ i_j^* 𝒪_{𝐏^{n_j}_{V_j}}(1)`.

Each member of the covering contributes `Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver`
— an immersion into projective space over the base pulling the hyperplane sheaf back to the
restriction of `L` — at the restricted morphism `f ∣_ V_j`, whose source is `f⁻¹(V_j)`. -/
def HasProjectiveImmersionCover {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] : Prop :=
  ∃ (ι : Type u) (V : ι → S.Opens), (⨆ j, V j) = ⊤ ∧ ∀ j : ι,
    HasImmersionTwistOver (f ∣_ V j)
      ((modulePullback (f ⁻¹ᵁ V j).ι.toLRSHom.toShHom).obj L)

/-- **Condition (2) of Stacks Tag 02NQ from its pointwise form**: if every point of the base has an
open neighbourhood `V` over which `L` is the hyperplane sheaf pulled back along an immersion into a
projective space over `V`, then those neighbourhoods are such a covering. -/
theorem hasProjectiveImmersionCover_of_forall {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L]
    (h : ∀ x : S, ∃ V : S.Opens, x ∈ V ∧ HasImmersionTwistOver (f ∣_ V)
      ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L)) :
    HasProjectiveImmersionCover f L := by
  choose V hxV hV using h
  exact ⟨↥S, V, eq_top_iff.mpr fun x _ => Opens.mem_iSup.mpr ⟨x, hxV x⟩, hV⟩

/-! ### The statement of Stacks Tag 01VT, (5) implies (3) -/

/-- **The statement of Stacks Tag 01VT, (5) implies (3)**: an immersion into `𝐏^n_S` over `S`
carrying the hyperplane sheaf to `L` exhibits `L` as relatively very ample. No condition on the
morphism or the base is imposed. It is proved as
`Stacks.VeryAmpleGlue.veryAmpleOfProjectiveImmersion`. -/
def VeryAmpleOfProjectiveImmersion : Prop :=
  ∀ (A B : Scheme.{u}) (g : A ⟶ B) (N : A.Modules) [IsInvertibleModule A N],
    HasImmersionTwistOver g N → Tag01VMVeryAmple.IsRelativelyVeryAmple g N

end Stacks.VeryAmpleFiniteTypeCover

end
