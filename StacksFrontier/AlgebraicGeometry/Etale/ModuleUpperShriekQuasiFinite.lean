module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLiftAdjunction
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleLift

import StacksCore.Tactic.StacksAttribute

/-!
# Upper shriek with coefficients in a ring

Let `f : X ⟶ Y` be a locally quasi-finite morphism of a big étale site and let `Λ` be a ring.
The direct image with compact support `f_! : Mod(X_étale, Λ) ⥤ Mod(Y_étale, Λ)` has a right
adjoint `f^! : Mod(Y_étale, Λ) ⥤ Mod(X_étale, Λ)`, and the abelian sheaf underlying `f^!G` is
the upper shriek of the abelian sheaf underlying `G`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.fUpperShriekMod` — the functor `f^!` on sheaves of
  `Λ`-modules.

## Main results

* `AlgebraicGeometry.SmallEtale.fShriekModAdjunction` — **the adjunction `f_! ⊣ f^!` on sheaves
  of `Λ`-modules**, and `AlgebraicGeometry.SmallEtale.fUpperShriekModForgetIso` the
  identification of `f^!` with the upper shriek of abelian sheaves on underlying abelian
  sheaves.

## Implementation notes

Both `f_!` and `f^!` on sheaves of `Λ`-modules are the lifts
`Stacks.ModuleCatLift.moduleLift` of their abelian counterparts: a sheaf of `Λ`-modules is an
abelian sheaf `F` together with a ring map `Λ → End F`, and an additive functor carries that
structure along. This is the source's construction, and it makes the agreement of the two upper
shrieks on underlying abelian sheaves an equality of functors rather than a comparison to be
proved. What remains is the adjunction, which is
`Stacks.ModuleCatLift.moduleLiftAdjunction`: the transpose of a `Λ`-linear morphism is
`Λ`-linear, so the hom-set bijection of the abelian adjunction restricts.

The coefficient universe is the cutoff `max (u + 1) v r` at which `f_!` is defined, `u` being
the universe of the schemes, and it is passed explicitly to the lift of the adjunction for the
reason recorded in `StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleLift`.

## References

* [Stacks Project, Tag 0F59](https://stacks.math.columbia.edu/tag/0F59)
* [Stacks Project, Tag 0F6R](https://stacks.math.columbia.edu/tag/0F6R)
* [Stacks Project, Tag 0F5F](https://stacks.math.columbia.edu/tag/0F5F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.SmallEtale

universe u v r

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ] {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- The upper shriek `f^! : Mod(Y_étale, Λ) ⥤ Mod(X_étale, Λ)` with coefficients in a ring `Λ`:
the `Λ`-linear lift of the upper shriek of abelian étale sheaves. -/
public def fUpperShriekMod : ModuleSheaf.{u, v, r} B Y Λ ⥤ ModuleSheaf.{u, v, r} B X Λ :=
  Stacks.ModuleCatLift.moduleLift.{max (u + 1) v r, r, _, _, _, _} Λ
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)
    (fUpperShriekFunctor.{u, max v r} B f)

/-- The direct image with compact support `f_!` of a locally quasi-finite morphism, on étale
sheaves of `Λ`-modules, is left adjoint to the upper shriek `f^!` with coefficients in `Λ`. -/
@[stacks 0F59 "part (3), f_! on étale sheaves of Λ-modules has a right adjoint f^!"]
public def fShriekModAdjunction :
    fShriekMod.{u, v, r} B Λ f ⊣ fUpperShriekMod.{u, v, r} B Λ f :=
  Stacks.ModuleCatLift.moduleLiftAdjunction.{max (u + 1) v r, r, _, _, _, _} Λ
    (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B Y.obj Y.property)
    (fShriekFunctor.{u, max v r} B f) (fUpperShriekFunctor.{u, max v r} B f)
    (fShriekAdjunction.{u, max v r} B f)

/-- The direct image with compact support on étale sheaves of `Λ`-modules has a right
adjoint. -/
public instance fShriekMod_isLeftAdjoint : (fShriekMod.{u, v, r} B Λ f).IsLeftAdjoint :=
  ⟨_, ⟨fShriekModAdjunction.{u, v, r} B Λ f⟩⟩

/-- The upper shriek with coefficients in `Λ` agrees with the upper shriek of abelian étale
sheaves on underlying abelian sheaves: the abelian sheaf underlying `f^!G` is `f^!` of the
abelian sheaf underlying `G`. -/
@[stacks 0F59 "part (3), the Λ-linear f^! agrees with f^! on underlying abelian sheaves"]
public def fUpperShriekModForgetIso :
    fUpperShriekMod.{u, v, r} B Λ f ⋙ forgetModuleSheaf.{u, v, r} B X Λ ≅
      forgetModuleSheaf.{u, v, r} B Y Λ ⋙ fUpperShriekFunctor.{u, max v r} B f :=
  Stacks.ModuleCatLift.moduleLiftForgetIso.{max (u + 1) v r, r, _, _, _, _} Λ
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)
    (fUpperShriekFunctor.{u, max v r} B f)

end AlgebraicGeometry.SmallEtale

end
