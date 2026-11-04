module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparison
public import StacksFrontier.AlgebraicGeometry.SectionsColimit.Basic
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsBaseChangeData

/-!
# The terms of the sequence of Stacks 07YH along a map of base rings

Let `q : W → S` carry a module `𝓕`, let `t : Spec A → S` be a scheme over `S` and let
`ψ : A → A₁` be a ring map, so that `g : W_{A₁} → W_A` is the induced morphism of base changes.
A semilinear map `M → N` from an `A`-module to an `A₁`-module along `ψ` — equivalently an
`A₁`-linear map `A₁ ⊗_A M → N` — induces

```
g^*(𝓕_A ⊗_A M) ⟶ 𝓕_{A₁} ⊗_{A₁} N.
```

This is the coefficient half of the map of obstruction modules of clause (2) of Stacks 07YG:
composed with the pullback map on cohomology it gives
`H¹(W_A, 𝓕_A ⊗_A M) → H¹(W_{A₁}, 𝓕_{A₁} ⊗_{A₁} N)`.

## Main definitions

* `Deformation.Artin.SectionsSheaf.ofSemilinear` — a semilinear map `M → N` along `ψ` read as a
  map `A₁ ⊗_A M → N`, which is the form the construction takes as input.
* `Deformation.Artin.SectionsSheaf.tildeFirstFactorMap` — the induced map on the first tensor
  factor, `g^*π_A^* M̃ ⟶ π_{A₁}^* Ñ`.
* `Deformation.Artin.SectionsSheaf.tensorSheafPullbackMap` — **the map
  `g^*(𝓕_A ⊗_A M) ⟶ 𝓕_{A₁} ⊗_{A₁} N`.**

## Implementation notes

The first factor is a chain of comparisons that already exist: `Scheme.Modules.pullbackComp`
and `pullbackCongr` move `g^*π_A^*` to `π_{A₁}^*(Spec ψ)^*` across the base-change square
(`commSqBase`, which is `baseChangeMap_comp_fst`), and
`Stacks.AlgebraicGeometry.SectionsColimit.tildePullbackIso` identifies `(Spec ψ)^* M̃` with
`(A₁ ⊗_A M)~`; then the given map is applied.

The two factors are combined by the comparison of [Stacks, Tag 01CD],
`Stacks.RingedSpace.comparisonIso`, which identifies `g^*(P ⊗ Q)` with `g^*P ⊗ g^*Q` and needs
no hypothesis, together with `baseChangeSheafIso` on the second factor. The product morphism is
written with `×ₘ`: supplying the pair directly fails, because the elaborator will not reduce
the `.1` of `Functor.prod ... |>.obj` when checking the first component.

`tensorSheafFunctor_obj_eq` converts between `Stacks.sheafTensorRight`, which
`tensorSheafFunctor` is built from, and the bifunctor spelling the comparison of Tag 01CD is
stated in; as elsewhere in this development the conversion is confined to the two ends.

## References

* [Stacks Project, Tag 07YH](https://stacks.math.columbia.edu/tag/07YH)
* [Stacks Project, Tag 07YG](https://stacks.math.columbia.edu/tag/07YG)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Prod

universe u

namespace Deformation.Artin.SectionsSheaf

section TensorPullback

variable {S : Scheme.{u}} {A A₁ : CommRingCat.{u}} (ψ : A ⟶ A₁) (t : Spec A ⟶ S)
  {W : Scheme.{u}} (q : W ⟶ S) (𝓕 : W.Modules)

/-- **A semilinear map along `ψ`, as a map out of the base change.** A morphism
`M ⟶ (restrictScalars ψ).obj N` of `A`-modules — that is, an `A`-linear map `M → N` where the
`A`-structure on the `A₁`-module `N` is restricted along `ψ`, which is the datum clause (2) of
Stacks 07YG quantifies over — is the same as an `A₁`-linear map `A₁ ⊗_A M → N`. -/
def ofSemilinear {M : ModuleCat.{u} A} {N : ModuleCat.{u} A₁}
    (α : M ⟶ (ModuleCat.restrictScalars ψ.hom).obj N) :
    (ModuleCat.extendScalars ψ.hom).obj M ⟶ N :=
  ((ModuleCat.extendRestrictScalarsAdj ψ.hom).homEquiv M N).symm α

/-- The two routes from `W_{A₁}` to `Spec A` agree: this is `baseChangeMap_comp_fst` in the
opaque spelling of the base-change data. -/
theorem commSqBase : baseChangeMap q (quotHom ψ t) ≫ topProj t q =
    botProj ψ t q ≫ Spec.map ψ :=
  baseChangeMap_comp_fst q (quotHom ψ t)

end TensorPullback

/-! ### The coefficient map with the base-change morphism of schemes as a parameter -/

section TensorPullbackGen

variable {A A₁ : CommRingCat.{u}} (ψ : A ⟶ A₁) {W X X₁ : Scheme.{u}} (π : X ⟶ Spec A)
  (s : X ⟶ W) (π₁ : X₁ ⟶ Spec A₁) (s₁ : X₁ ⟶ W) (𝓕 : W.Modules) (g : X₁ ⟶ X)

/-- **`g^* 𝓕_A ≅ 𝓕_{A₁}`** for any morphism `g : W_{A₁} → W_A` over `W`: both are the pullback
of `𝓕` along a projection to `W`, and the two projections agree by hypothesis. This is
`Deformation.Artin.SectionsSheaf.baseChangeSheafIso` with the two base changes abstracted to
schemes over `W` and the base-change immersion to a morphism of schemes. -/
def baseChangeSheafIsoGen (hsnd : g ≫ s = s₁) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback s).obj 𝓕) ≅
      (Scheme.Modules.pullback s₁).obj 𝓕 :=
  (Scheme.Modules.pullbackComp g s ≪≫ Scheme.Modules.pullbackCongr hsnd).app 𝓕

/-- **The induced map on the first tensor factor**, `g^*π_A^* M̃ ⟶ π_{A₁}^* Ñ`, with the two
base changes abstracted to schemes over `Spec A` resp. `Spec A₁` and the base-change morphism
of schemes as a parameter. -/
def tildeFirstFactorMapGen (hfst : g ≫ π = π₁ ≫ Spec.map ψ) {M : ModuleCat.{u} A}
    {N : ModuleCat.{u} A₁} (α : (ModuleCat.extendScalars ψ.hom).obj M ⟶ N) :
    (Scheme.Modules.pullback g).obj
        ((Scheme.Modules.pullback π).obj ((tilde.functor A).obj M)) ⟶
      (Scheme.Modules.pullback π₁).obj ((tilde.functor A₁).obj N) :=
  ((Scheme.Modules.pullbackComp g π).app ((tilde.functor A).obj M) ≪≫
      (Scheme.Modules.pullbackCongr hfst).app ((tilde.functor A).obj M) ≪≫
      ((Scheme.Modules.pullbackComp π₁ (Spec.map ψ)).app ((tilde.functor A).obj M)).symm ≪≫
      (Scheme.Modules.pullback π₁).mapIso
        ((Stacks.AlgebraicGeometry.SectionsColimit.tildePullbackIso ψ).app M)).hom ≫
    (Scheme.Modules.pullback π₁).map ((tilde.functor A₁).map α)

/-- **The map `g^*(𝓕_A ⊗_A M) ⟶ 𝓕_{A₁} ⊗_{A₁} N`** induced by a map `A₁ ⊗_A M → N`, with the
two base changes abstracted to schemes over `Spec A` resp. `Spec A₁` and over `W`, and the
base-change morphism of schemes `g` as a parameter: the two squares `g` is asked to make
commute — over `Spec A` and over `W` — are the hypotheses, and are all the construction uses of
the base-change immersion.

Carrying `g` as a parameter is what makes the coherence of clause (2) of Stacks 07YG *statable*
at an identity: the base-change immersion attached to an identity morphism of affine objects is
the transport `eqToHom` of an equality of fibre products and not `𝟙`, and for a morphism that
is not `𝟙` the pushforward is not `𝟭`, so the degeneration of the pullback–pushforward
adjunction cannot even be written down. Abstracting the fibre products to opaque schemes is
what keeps the resulting definitional comparisons cheap: a statement in which the base changes
are spelled out as `pullback`s asks the kernel to unfold `Limits.getLimitCone`. See the "what is
not done" of `StacksFrontier/Deformation/Artin/Obstruction/SectionsObstructionMap.lean`. -/
def tensorSheafPullbackMapGen (hfst : g ≫ π = π₁ ≫ Spec.map ψ) (hsnd : g ≫ s = s₁)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} A₁}
    (α : (ModuleCat.extendScalars ψ.hom).obj M ⟶ N) :
    (Scheme.Modules.pullback g).obj
        ((tensorSheafFunctor π ((Scheme.Modules.pullback s).obj 𝓕)).obj M) ⟶
      (tensorSheafFunctor π₁ ((Scheme.Modules.pullback s₁).obj 𝓕)).obj N :=
  eqToHom (congrArg (fun Z => (Scheme.Modules.pullback g).obj Z)
      (tensorSheafFunctor_obj_eq π ((Scheme.Modules.pullback s).obj 𝓕) M)) ≫
    ((Stacks.RingedSpace.comparisonIso g.toLRSHom.toShHom).app
      ((Scheme.Modules.pullback π).obj ((tilde.functor A).obj M),
        (Scheme.Modules.pullback s).obj 𝓕)).hom ≫
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X₁.toRingedSpace)).presheaf, ((X₁.toRingedSpace)).IsSheaf⟩))).map
      (tildeFirstFactorMapGen ψ π π₁ g hfst α ×ₘ (baseChangeSheafIsoGen s s₁ 𝓕 g hsnd).hom) ≫
    eqToHom (tensorSheafFunctor_obj_eq π₁ ((Scheme.Modules.pullback s₁).obj 𝓕) N).symm

end TensorPullbackGen

section TensorPullback

variable {S : Scheme.{u}} {A A₁ : CommRingCat.{u}} (ψ : A ⟶ A₁) (t : Spec A ⟶ S)
  {W : Scheme.{u}} (q : W ⟶ S) (𝓕 : W.Modules)

/-- **The induced map on the first tensor factor**, `g^*π_A^* M̃ ⟶ π_{A₁}^* Ñ`: transport the
pullback across the base-change square, identify `(Spec ψ)^* M̃` with `(A₁ ⊗_A M)~`, and apply
the given map. -/
def tildeFirstFactorMap {M : ModuleCat.{u} A} {N : ModuleCat.{u} A₁}
    (α : (ModuleCat.extendScalars ψ.hom).obj M ⟶ N) :
    (Scheme.Modules.pullback (baseChangeMap q (quotHom ψ t))).obj
        ((Scheme.Modules.pullback (topProj t q)).obj ((tilde.functor A).obj M)) ⟶
      (Scheme.Modules.pullback (botProj ψ t q)).obj ((tilde.functor A₁).obj N) :=
  tildeFirstFactorMapGen ψ (topProj t q) (botProj ψ t q) (baseChangeMap q (quotHom ψ t))
    (commSqBase ψ t q) α

/-- **The map `g^*(𝓕_A ⊗_A M) ⟶ 𝓕_{A₁} ⊗_{A₁} N`** induced by a map `A₁ ⊗_A M → N`. This is the
coefficient half of the map of obstruction modules of clause (2) of Stacks 07YG: the pullback
along `g : W_{A₁} → W_A` of the term `𝓕_A ⊗_A M` of the sheaf-level sequence over `A`, mapped to
the term `𝓕_{A₁} ⊗_{A₁} N` of the sequence over `A₁`. -/
def tensorSheafPullbackMap {M : ModuleCat.{u} A} {N : ModuleCat.{u} A₁}
    (α : (ModuleCat.extendScalars ψ.hom).obj M ⟶ N) :
    (Scheme.Modules.pullback (baseChangeMap q (quotHom ψ t))).obj
        ((tensorSheafFunctor (topProj t q) (topSheaf t q 𝓕)).obj M) ⟶
      (tensorSheafFunctor (botProj ψ t q) (botSheaf ψ t q 𝓕)).obj N :=
  tensorSheafPullbackMapGen ψ (topProj t q) (pullback.snd (Over.mk t).hom q) (botProj ψ t q)
    (pullback.snd (quotOver ψ t).hom q) 𝓕 (baseChangeMap q (quotHom ψ t)) (commSqBase ψ t q)
    (baseChangeMap_comp_snd q (quotHom ψ t)) α

end TensorPullback

end Deformation.Artin.SectionsSheaf

end
