module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves

/-!
# Restriction of a torsion abelian sheaf along a cocontinuous functor of sites

Let `u : 𝒟 ⥤ 𝒞` be a continuous and cocontinuous functor of sites. Restriction of abelian
sheaves along `u` — which on sections is `(u^s F)(V) = F(u V)` — carries torsion abelian sheaves
to torsion abelian sheaves.

Being torsion is the local condition of [Stacks, Tag 0DD7]: every section is, on some covering
sieve, annihilated by a positive integer. A section of `u^s F` over `V` is a section of `F` over
`u V`, so it is annihilated on a covering sieve `R` of `u V`; cocontinuity of `u` says exactly
that the pullback of `R` along `u` is a covering sieve of `V`, and along each of its members the
section restricts to a restriction of the original one.

## Main results

* `Stacks.Torsion.torsionSheafProperty_sheafPushforwardContinuous`: the statement above.

## References

* [Stacks Project, Tag 0DD7](https://stacks.math.columbia.edu/tag/0DD7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Torsion

universe w v₁ u₁ v₂ u₂

/-- **Restriction along a cocontinuous functor of sites preserves torsion abelian sheaves.** A
section of the restriction `u^s F` over `V` is a section of `F` over `u V`, so a covering sieve
of `u V` annihilates it; the pullback of that sieve along `u` covers `V` because `u` is
cocontinuous. -/
theorem torsionSheafProperty_sheafPushforwardContinuous
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {J : GrothendieckTopology D} {K : GrothendieckTopology C}
    (u : D ⥤ C) [u.IsContinuous J K] [u.IsCocontinuous J K]
    (F : Sheaf K AddCommGrpCat.{w}) (hF : torsionSheafProperty K F) :
    torsionSheafProperty J ((u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj F) := by
  intro V x
  obtain ⟨R, hR, hkill⟩ := hF (u.obj V) x
  refine ⟨R.functorPullback u, u.cover_lift J K hR, ?_⟩
  intro W g hg
  exact hkill (u.obj W) (u.map g) hg

end Stacks.Torsion

end
