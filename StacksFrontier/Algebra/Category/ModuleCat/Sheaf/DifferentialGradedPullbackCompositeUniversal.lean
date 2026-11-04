module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPushforward

/-!
# The unit of a pullback is universal for a further morphism of ringed sites

`SheafOfModules.DifferentialGradedModule.SemilinearHom.IsUniversal` asks of the unit
`θ : ℳ ⟶ g^*ℳ` of a pullback along `g` that composition with it identify the `φ`-semilinear
maps `g^*ℳ ⟶ 𝒩` with the `ψ ∘ φ`-semilinear maps `ℳ ⟶ 𝒩`, for `φ` a semilinear homomorphism
along a second morphism of ringed sites `f`. It is what makes pullback along a composite the
composite of the two pullbacks, `PullbackData.transIso`, and through that it was a hypothesis of
every statement about derived pullback along a composition.

It is not a hypothesis: it holds for the unit of *every* pullback datum. Three bijections
compose. A `φ`-semilinear map `g^*ℳ ⟶ 𝒩` is a morphism `g^*ℳ ⟶ f_*𝒩` of right differential
graded modules, which is `semilinearHomEquiv`. Morphisms `g^*ℳ ⟶ 𝒯` are the `ψ`-semilinear maps
`ℳ ⟶ 𝒯`, which is the universal property of the pullback, `IsPullback.homEquiv`. And a
`ψ`-semilinear map `ℳ ⟶ f_*𝒩` *is* a `ψ ∘ φ`-semilinear map `ℳ ⟶ 𝒩`: on local sections the two
are the same family of maps `ℳ(V) ⟶ 𝒩(f(g(V)))`, and the two conditions relating them to the
actions agree because the action of `𝒜'` on `f_*𝒩` is the action of `𝒜` through `φ`. That last
identification is `semilinearHomPushforwardEquiv`, an equivalence which is the identity on every
field.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.semilinearHomPushforwardEquiv`: a `ψ`-semilinear map
  into the direct image `f_*𝒩` is a `ψ ∘ φ`-semilinear map into `𝒩`.

## Main results

* `SheafOfModules.DifferentialGradedModule.PullbackData.isUniversal_unit`: **the unit of a
  pullback datum is universal for a further morphism of ringed sites.**

## Implementation notes

The direct image of right differential graded modules is defined on sheaves of modules in one
universe, so the three sites' modules live in a single universe here. That is the setting of the
pullback-pushforward adjunction of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPushforward.lean`, which this
file sits beside.

Continuity of the two functors of sites is what makes the direct image of a sheaf of modules a
sheaf, so it appears as the instance hypotheses `[w.IsContinuous J' J]` and
`[x.IsContinuous J'' J']`; both are part of presenting a morphism of ringed topoi by a functor
of sites.

## References

* [Stacks Project, Tag 0FTI](https://stacks.math.columbia.edu/tag/0FTI)
* [Stacks Project, Tag 0FTE](https://stacks.math.columbia.edu/tag/0FTE)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
-/

@[expose] public section

open CategoryTheory

universe t a a' a'' m v u v' u' v'' u''

namespace SheafOfModules

namespace DifferentialGradedModule

section Composite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}
  {C'' : Type u''} [Category.{v''} C''] {J'' : GrothendieckTopology C''}
  {R'' : Sheaf J'' RingCat.{t}}
  {w : C' ⥤ C} [w.IsContinuous J' J] {σ : R'.obj ⟶ w.op ⋙ R.obj}
  {x : C'' ⥤ C'} [x.IsContinuous J'' J'] {τ : R''.obj ⟶ x.op ⋙ R'.obj}
  {A : DifferentialGradedAlgebra.{t, a} R} {A' : DifferentialGradedAlgebra.{t, a'} R'}
  {A'' : DifferentialGradedAlgebra.{t, a''} R''}
  {φ : DifferentialGradedAlgebra.SemilinearHom w σ A' A}
  {ψ : DifferentialGradedAlgebra.SemilinearHom x τ A'' A'}

/-- **A `ψ`-semilinear map into the direct image `f_*𝒩` is a `ψ ∘ φ`-semilinear map into `𝒩`.**
On local sections both are a family of additive maps `ℳ(V) ⟶ 𝒩(f(g(V)))`; the two are
semilinear over the same map of structure sheaves, commute with the same differentials, and
intertwine the actions in the same way, because a homogeneous section `b` of `𝒜''` acts on
`f_*𝒩` through `φ(ψ(b))`. So the equivalence is the identity on every field. -/
def semilinearHomPushforwardEquiv (M : DifferentialGradedModule.{t, a'', m} A'')
    (N : DifferentialGradedModule.{t, a, m} A) :
    SemilinearHom ψ M (pushforwardObj φ N) ≃ SemilinearHom (ψ.trans φ) M N where
  toFun θ :=
    { app := θ.app
      map_smul := θ.map_smul
      naturality := θ.naturality
      comm_d := θ.comm_d
      map_mul := θ.map_mul }
  invFun θ :=
    { app := θ.app
      map_smul := θ.map_smul
      naturality := θ.naturality
      comm_d := θ.comm_d
      map_mul := θ.map_mul }
  left_inv _ := rfl
  right_inv _ := rfl

omit [x.IsContinuous J'' J'] in
/-- The equivalence is the identity on local sections. -/
@[simp]
theorem semilinearHomPushforwardEquiv_app (M : DifferentialGradedModule.{t, a'', m} A'')
    (N : DifferentialGradedModule.{t, a, m} A) (θ : SemilinearHom ψ M (pushforwardObj φ N))
    (i : ℤ) (V : C''ᵒᵖ) (y : (M.complex.X i).val.obj V) :
    (semilinearHomPushforwardEquiv M N θ).app i V y = θ.app i V y :=
  rfl

/-- **The unit of a pullback datum is universal for a further morphism of ringed sites.**
Composition with the unit `ℳ ⟶ g^*ℳ` identifies the `φ`-semilinear maps `g^*ℳ ⟶ 𝒩` with the
`ψ ∘ φ`-semilinear maps `ℳ ⟶ 𝒩`: the first are the morphisms `g^*ℳ ⟶ f_*𝒩`, those are the
`ψ`-semilinear maps `ℳ ⟶ f_*𝒩` by the universal property of the pullback, and those are the
`ψ ∘ φ`-semilinear maps `ℳ ⟶ 𝒩`. -/
noncomputable def PullbackData.isUniversal_unit (Pψ : PullbackData.{t, a', m, v', u', a'', m} ψ)
    (M : DifferentialGradedModule.{t, a'', m} A'')
    (N : DifferentialGradedModule.{t, a, m} A) :
    (Pψ.unit M).IsUniversal φ N where
  transEquiv :=
    (semilinearHomEquiv φ (Pψ.obj M) N).trans
      (((Pψ.isPullback M).homEquiv (pushforwardObj φ N)).trans
        (semilinearHomPushforwardEquiv M N))
  transEquiv_apply _ := rfl

end Composite

end DifferentialGradedModule

end SheafOfModules

end
