module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedModuleMonoidal
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 06VE (7) at `τ = étale`, as an isomorphism of bifunctors

Clause (7) of Descent, Lemma 06VE says that the comparison `𝓕 ↦ 𝓕^a` of Descent,
Proposition 03DX carries a tensor product to a tensor product: for `𝒪_S`-modules `𝓕`, `𝓖` on a
scheme `S`,

`(𝓕 ⊗_{𝒪_S} 𝓖)^a = 𝓕^a ⊗_𝒪 𝓖^a`.

`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleAssociatedModuleMonoidal.lean`
proves the clause at `τ = étale` objectwise, as
`AlgebraicGeometry.SmallEtale.associatedModuleTensorIso`, and claims no tag for it: read as an
instance of Stacks 03EL at one morphism of ringed topoi it is a statement about the pullback
functor, and 03EL is already registered on `Stacks.SheafOfModules.pullbackTensorIso`.  Read
instead as a statement about `𝓕 ↦ 𝓕^a` it is exactly clause (7) of 06VE, which the tree carries
at `τ = Zariski` (`AlgebraicGeometry.SmallZariski.associatedModuleTensorIsoOfComparison`) and on
the big sites (`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso`) but nowhere at
`τ = étale`.  This file supplies the étale entry of that row, and the attribute sits here so that
the monoidal file keeps its stated intent of claiming nothing.

## Main results

* `AlgebraicGeometry.SmallEtale.associatedModuleTensorBifunctorIso`: **Stacks 06VE (7) at
  `τ = étale`** for all `𝒪_S`-modules, as an isomorphism of bifunctors
  `(- ⊗ -) ⋙ ε^* ≅ (ε^* × ε^*) ⋙ (- ⊗ -)`, i.e. the clause together with its naturality in the
  pair `(𝓕, 𝓖)`.
* `AlgebraicGeometry.SmallEtale.associatedModuleTensorBifunctorIso_app`: its component at
  `(𝓕, 𝓖)` is `AlgebraicGeometry.SmallEtale.associatedModuleTensorIso`, the objectwise form in
  which the source states the clause.  No second objectwise comparison is built here.

## Implementation notes

The two tensor products are written at the bifunctor spelling of Stacks 03EL,
`Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor O)` over the structure sheaf of
each of the two ringed sites, which is both the spelling 03EL is stated with and the one the
body produces, so nothing has to be transported; the monoidal file's
`tensorSheafBifunctorZariski_obj` and `tensorSheafBifunctorEtale_obj` identify that spelling with
the consumers' on objects.

`associatedModuleTensorBifunctorIso_app`'s two sides differ only in
`(NatIso.prod ε ε).hom.app (𝓕, 𝓖)` against `(Iso.prod (ε.app 𝓕) (ε.app 𝓖)).hom`, which are the
same pair of components.  Deciding that under the *named* isomorphisms is not cheap: it whnfs the
two composites through the sheaf-of-modules structures they are built over, unfolding
`CategoryTheory.SheafOfModules.forget` and the ringed-topos morphism behind `ε`.  So the
identification is made once and for all at parameters, in
`AlgebraicGeometry.SmallEtale.isoWhiskerLeft_trans_isoWhiskerRight_prod_app`, where there is
nothing to unfold, and this lemma is that one instantiated.  The alternative would be to build a
second objectwise comparison here instead of reusing the monoidal file's, which is the duplication
this file exists to avoid.

The statement is made for **all** `𝒪_S`-modules, not only quasi-coherent ones.  The source states
clause (7) for quasi-coherent `𝓕`, `𝓖`, and the quasi-coherent case is this one restricted along
`CategoryTheory.ObjectProperty.ι`; nothing in the argument uses quasi-coherence, since it is a
property of the pullback functor.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u u₁ u₂ v₁ v₂

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06VE (7) at `τ = étale`.**  The functor `𝓕 ↦ 𝓕^a` into the `𝒪`-modules of the small
étale site of `S` carries the tensor product of two `𝒪_S`-modules to the tensor product of their
images:

`(𝓕 ⊗_{𝒪_S} 𝓖)^a ≅ 𝓕^a ⊗_𝒪 𝓖^a`,

naturally in the pair `(𝓕, 𝓖)`, with no hypothesis on `𝓕` or `𝓖`.

This is Modules on Sites, Lemma 03EL — `Stacks.SheafOfModules.pullbackTensorIso` — for the
morphism of ringed topoi underlying `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` of Stacks 070R and 08H7,
conjugated on both sides by `AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso`.  Its
component at a pair is the objectwise form in which the source states the clause,
`AlgebraicGeometry.SmallEtale.associatedModuleTensorIso`, by
`AlgebraicGeometry.SmallEtale.associatedModuleTensorBifunctorIso_app`.

With `AlgebraicGeometry.SmallZariski.associatedModuleTensorIsoOfComparison` at `τ = Zariski` and
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso` on the big sites, clause (7) is
covered at every functor the lemma quantifies over. -/
@[stacks 06VE "part (7), small site at τ = étale, for all 𝒪_S-modules; bifunctor form, whose \
components are the objectwise form in which the source states the clause"]
def associatedModuleTensorBifunctorIso :
    Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          S.zariskiRingedSite.toRingedTopos.O) ⋙ associatedModule B S hS ≅
      Functor.prod (associatedModule B S hS) (associatedModule B S hS) ⋙
        Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedSite B S hS).toRingedTopos.O) :=
  Functor.isoWhiskerLeft _ (pullbackModulesToZariskiIso B S hS).symm ≪≫
    Stacks.SheafOfModules.pullbackTensorIso (toZariskiRingedToposModulesHom B S hS) ≪≫
    Functor.isoWhiskerRight
      (NatIso.prod (pullbackModulesToZariskiIso B S hS)
        (pullbackModulesToZariskiIso B S hS)) _

/-- **A bifunctor isomorphism conjugated by a natural isomorphism, read at a pair.**  For
`e : F ≅ F'` and `θ : uncurry Tz ⋙ F ≅ (F × F) ⋙ uncurry Te` with `Tz` and `Te` *curried*
bifunctors, the component at `(M, N)` of the composite
`uncurry Tz ⋙ F' ≅ uncurry Tz ⋙ F ≅ (F × F) ⋙ uncurry Te ≅ (F' × F') ⋙ uncurry Te` is the
composite of the components, the last factor read in the curried form in which the objectwise
statements of this development are written.

Everything here is a parameter, and that is what makes the proof cheap: the two sides differ only
in `(NatIso.prod e e).hom.app (M, N)` carried by `Functor.uncurry` against the two curried
factors `(Te.mapIso (e.app M)).app _` and `(Te.obj _).mapIso (e.app N)`, which is the definition
of `Functor.uncurry` on morphisms, so with `e` and `θ` opaque there is nothing left to reduce. -/
theorem isoWhiskerLeft_trans_isoWhiskerRight_prod_app {C₁ : Type u₁} [Category.{v₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] (Tz : C₁ ⥤ C₁ ⥤ C₁) (Te : C₂ ⥤ C₂ ⥤ C₂)
    {F F' : C₁ ⥤ C₂} (e : F ≅ F')
    (θ : Functor.uncurry.obj Tz ⋙ F ≅ Functor.prod F F ⋙ Functor.uncurry.obj Te) (M N : C₁) :
    (Functor.isoWhiskerLeft (Functor.uncurry.obj Tz) e.symm ≪≫ θ ≪≫
        Functor.isoWhiskerRight (NatIso.prod e e) (Functor.uncurry.obj Te)).app (M, N) =
      e.symm.app ((Functor.uncurry.obj Tz).obj (M, N)) ≪≫ θ.app (M, N) ≪≫
        ((Te.mapIso (e.app M)).app (F.obj N) ≪≫
          (Te.obj (F'.obj M)).mapIso (e.app N)) :=
  Iso.ext rfl

/-- The bifunctor form of Stacks 06VE (7) at `τ = étale` has as its components the objectwise
form, `AlgebraicGeometry.SmallEtale.associatedModuleTensorIso`: the two are the same composite,
whiskered in the one case and applied at a pair in the other. -/
theorem associatedModuleTensorBifunctorIso_app (M N : S.Modules) :
    (associatedModuleTensorBifunctorIso B S hS).app (M, N) =
      associatedModuleTensorIso B S hS M N :=
  isoWhiskerLeft_trans_isoWhiskerRight_prod_app
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      S.zariskiRingedSite.toRingedTopos.O)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedSite B S hS).toRingedTopos.O)
    (pullbackModulesToZariskiIso B S hS)
    (Stacks.SheafOfModules.pullbackTensorIso (toZariskiRingedToposModulesHom B S hS)) M N

end AlgebraicGeometry.SmallEtale

end
