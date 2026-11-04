module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIdentity
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsFirstFactorIdentity

/-!
# The coefficient half of the map of obstruction modules of Stacks 07YH at an identity

`Deformation.Artin.SectionsSheaf.tensorSheafPullbackMapGen` is the coefficient half of the map of
obstruction modules of clause (2) of Stacks 07YG for the example of Stacks 07YH. Its two tensor
factors degenerate at an identity morphism of schemes and the identity ring map, and those two
degenerations are proved — `unit_comp_tildeFirstFactorMapGen_id` and
`unit_comp_baseChangeSheafIsoGen_id`. This file carries the unit of the pullback--pushforward
adjunction past the two `eqToHom`s and the product morphism that the coefficient map wraps them
in, which is what the identity case of clause (2) asks for.

## Main results

* `Deformation.Artin.SectionsSheaf.tensorAssemble` — **the assembly, in the abstract**: a tensor
  bifunctor `L`, an endofunctor `G` with a unit, the comparison `G(L(P,Q)) ⟶ L(GP, GQ)` and a
  morphism of pairs out of `(GP, GQ)`, wrapped in two arrows that are identities, compose to `L`
  of the pair of composites.
* `Deformation.Artin.SectionsSheaf.tensorSheafFunctor_map_eq` — `M ↦ 𝓕 ⊗_A M` on morphisms, in
  the bifunctor spelling: the tensor of the pullback of the associated sheaf with the identity of
  `𝓕`. The companion of `tensorSheafFunctor_obj_eq`.
* `Deformation.Artin.SectionsSheaf.unit_comp_tensorSheafPullbackMapGen_id` — **the coefficient
  half of the map of obstruction modules at an identity**: the unit of the pullback--pushforward
  adjunction at `𝟙 X` followed by `g^*(𝓕_A ⊗_A M) ⟶ 𝓕_{A₁} ⊗_{A₁} N` at `g = 𝟙 X` and the
  identity ring map is `𝓕_A ⊗_A f`. This is the hypothesis `hα` of
  `Deformation.Artin.SectionsSheaf.obstructionMapGen_id`.
* `Deformation.Artin.SectionsSheaf.obstructionMapGen_id_of_semilinear` — consequently the identity
  case of the map of obstruction modules, **unconditionally**: `obstructionMapGen` at `g = 𝟙 X`
  and the identity ring map is `Hⁿ(X, 𝓕_A ⊗_A f)`.

## Implementation notes

The three steps of `unit_comp_tensorSheafPullbackMapGen_id` are each confined to a declaration of
their own, and that is the cure used throughout this development: the two spellings
of one object — `(tensorSheafFunctor π 𝓕_X).obj M` against
`(Stacks.RingedSpace.tensorSheaf X.toRingedSpace).obj (π^* M̃, 𝓕_X)`, and `X.ringCatSheaf` against
`structureRingSheaf X.toRingedSpace` — are definitionally equal and not syntactically, so each
comparison must be made where the elaborator has the full definitional unfolding available.

`tensorAssemble` therefore takes **every** arrow as a variable, including the two `eqToHom`s,
which it is told are identities by hypothesis rather than inspecting: the unifier then matches its
conclusion against the goal first-order and the one definitional comparison per arrow is made at
the application. Both `eqToHom`s are `eqToHom` of an equality whose two sides are definitionally
equal, so `CategoryTheory.eqToHom_refl` discharges those hypotheses.

The product morphism is taken apart by `CategoryTheory.Prod.hom_ext`: composition in a product
category is componentwise by `rfl`, so the two factor-wise degenerations are the two components
with no further step.

## References

* [Stacks Project, Tag 07YH](https://stacks.math.columbia.edu/tag/07YH)
* [Stacks Project, Tag 07YG](https://stacks.math.columbia.edu/tag/07YG)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Prod

universe u

namespace Deformation.Artin.SectionsSheaf

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### The assembly, in the abstract -/

/-- **The unit, the comparison of a tensor product and a morphism of pairs, assembled.** For a
bifunctor `L`, an endofunctor `G` with arrows `η₀ : L(P,Q) ⟶ G(L(P,Q))`, `ηP : P ⟶ GP` and
`ηQ : Q ⟶ GQ`, a comparison `C : G(L(P,Q)) ⟶ L(GP, GQ)` satisfying `η₀ ≫ C = L(ηP, ηQ)`, and a
morphism of pairs `m` out of `(GP, GQ)`, the composite `η₀ ≫ C ≫ L.map m` is `L` of
`(ηP, ηQ) ≫ m` — wrapped, on either side, in an arrow that is the identity.

Every arrow is a variable constrained by an equation rather than written out, the two transports
included. That is what makes the lemma applicable: the two spellings of the tensor product of
sheaves of modules on a scheme are definitionally equal and not syntactically, so a conclusion
written out in one of them would not match a goal written in the other first-order. -/
theorem tensorAssemble {𝒞 : Type*} [Category 𝒞] {P Q P' Q' : 𝒞}
    (L : 𝒞 × 𝒞 ⥤ 𝒞) (G : 𝒞 ⥤ 𝒞)
    (η₀ : L.obj (P, Q) ⟶ G.obj (L.obj (P, Q)))
    (ηP : P ⟶ G.obj P) (ηQ : Q ⟶ G.obj Q)
    (e₁ : G.obj (L.obj (P, Q)) ⟶ G.obj (L.obj (P, Q)))
    (C : G.obj (L.obj (P, Q)) ⟶ L.obj (G.obj P, G.obj Q))
    (m : ((G.obj P, G.obj Q) : 𝒞 × 𝒞) ⟶ (P', Q'))
    (e₂ : L.obj (P', Q') ⟶ L.obj (P', Q'))
    (w : ((P, Q) : 𝒞 × 𝒞) ⟶ (P', Q'))
    (he₁ : e₁ = 𝟙 _) (he₂ : e₂ = 𝟙 _)
    (hC : η₀ ≫ C = L.map (ηP ×ₘ ηQ))
    (hm : (ηP ×ₘ ηQ : ((P, Q) : 𝒞 × 𝒞) ⟶ (G.obj P, G.obj Q)) ≫ m = w) :
    η₀ ≫ e₁ ≫ C ≫ L.map m ≫ e₂ = L.map w := by
  subst he₁
  subst he₂
  simp only [Category.id_comp, Category.comp_id]
  rw [← Category.assoc, hC, ← L.map_comp, hm]

/-! ### The coefficient map at an identity -/

section Coefficient

variable {A : CommRingCat.{u}} {W X : Scheme.{u}} (π : X ⟶ Spec A) (s : X ⟶ W)
  (𝓕 : W.Modules)

/-- **`M ↦ 𝓕 ⊗_A M` on morphisms, in the bifunctor spelling**: the tensor product of the
pullback of the associated sheaf of the map with the identity of `𝓕`. The companion of
`Deformation.Artin.SectionsSheaf.tensorSheafFunctor_obj_eq`.

The functor tensors on the right by `𝓕`, so its value on a morphism is one sheafified
`PresheafOfModules.tensorHom`; the uncurried bifunctor composes two of them, and
`Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map` is the one step that merges the pair. -/
theorem tensorSheafFunctor_map_eq (F : SheafOfModules.{u} X.ringCatSheaf)
    {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    (tensorSheafFunctor π F).map f =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩))).map
        ((Scheme.Modules.pullback π).map ((tilde.functor A).map f) ×ₘ 𝟙 F) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
    ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩
    ((Scheme.Modules.pullback π).map ((tilde.functor A).map f)) (𝟙 F)).symm

/-- **The coefficient half of the map of obstruction modules of Stacks 07YH degenerates at an
identity.** The unit of the pullback--pushforward adjunction at `𝟙 X`, followed by the map
`g^*(𝓕_A ⊗_A M) ⟶ 𝓕_{A₁} ⊗_{A₁} N` at `g = 𝟙 X`, the identity ring map and the semilinear map
`f` read through `ofSemilinear`, is `𝓕_A ⊗_A f`.

This is the hypothesis `hα` of `Deformation.Artin.SectionsSheaf.obstructionMapGen_id`, and with
it the identity case of clause (2) of Stacks 07YG holds unconditionally. Its two tensor factors
are `Deformation.Artin.SectionsSheaf.unit_comp_tildeFirstFactorMapGen_id` and
`..unit_comp_baseChangeSheafIsoGen_id`; what is done here is carrying the unit past the two
`eqToHom`s of `tensorSheafFunctor_obj_eq` and the product morphism that the coefficient map wraps
them in, through `Stacks.RingedSpace.unit_comp_comparisonIso_id` for [Stacks, Tag 01CD]. -/
theorem unit_comp_tensorSheafPullbackMapGen_id
    (hfst : (𝟙 X : X ⟶ X) ≫ π = π ≫ Spec.map (𝟙 A)) (hsnd : (𝟙 X : X ⟶ X) ≫ s = s)
    {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    pullbackIdUnit X ((tensorSheafFunctor π ((Scheme.Modules.pullback s).obj 𝓕)).obj M) ≫
        tensorSheafPullbackMapGen (𝟙 A) π s π s 𝓕 (𝟙 X) hfst hsnd (ofSemilinear (𝟙 A) f) =
      (tensorSheafFunctor π ((Scheme.Modules.pullback s).obj 𝓕)).map f :=
  (tensorAssemble ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩)))
        (Scheme.Modules.pullback (𝟙 X))
        (pullbackIdUnit X ((tensorSheafFunctor π ((Scheme.Modules.pullback s).obj 𝓕)).obj M))
        (pullbackIdUnit X ((Scheme.Modules.pullback π).obj ((tilde.functor A).obj M)))
        (pullbackIdUnit X ((Scheme.Modules.pullback s).obj 𝓕))
        (eqToHom (congrArg (fun Z => (Scheme.Modules.pullback (𝟙 X)).obj Z)
          (tensorSheafFunctor_obj_eq π ((Scheme.Modules.pullback s).obj 𝓕) M)))
        ((Stacks.RingedSpace.comparisonIso (𝟙 X : X ⟶ X).toLRSHom.toShHom).app
            ((Scheme.Modules.pullback π).obj ((tilde.functor A).obj M),
              (Scheme.Modules.pullback s).obj 𝓕)).hom
        (tildeFirstFactorMapGen (𝟙 A) π π (𝟙 X) hfst (ofSemilinear (𝟙 A) f) ×ₘ
          (baseChangeSheafIsoGen s s 𝓕 (𝟙 X) hsnd).hom)
        (eqToHom (tensorSheafFunctor_obj_eq π ((Scheme.Modules.pullback s).obj 𝓕) N).symm)
        ((Scheme.Modules.pullback π).map ((tilde.functor A).map f) ×ₘ
          𝟙 ((Scheme.Modules.pullback s).obj 𝓕))
        (eqToHom_refl _ _) (eqToHom_refl _ _)
        (Stacks.RingedSpace.unit_comp_comparisonIso_id X.toRingedSpace _ _)
        (CategoryTheory.Prod.hom_ext (unit_comp_tildeFirstFactorMapGen_id π hfst f)
          (unit_comp_baseChangeSheafIsoGen_id s 𝓕 hsnd))).trans
    (tensorSheafFunctor_map_eq π ((Scheme.Modules.pullback s).obj 𝓕) f).symm

/-- **The identity case of the map of obstruction modules of clause (2), unconditionally.**
`obstructionMapGen` at `g = 𝟙 X`, the identity ring map and a semilinear map read through
`ofSemilinear` is `Hⁿ(X, 𝓕_A ⊗_A f)`, which is what `map_id` and `map_local` of clause (2) of
Stacks 07YG ask for.

This is `Deformation.Artin.SectionsSheaf.obstructionMapGen_id` with its hypothesis `hα`
discharged by `unit_comp_tensorSheafPullbackMapGen_id`. -/
theorem obstructionMapGen_id_of_semilinear (n : ℕ)
    (hfst : (𝟙 X : X ⟶ X) ≫ π = π ≫ Spec.map (𝟙 A)) (hsnd : (𝟙 X : X ⟶ X) ≫ s = s)
    {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    obstructionMapGen (𝟙 A) π s π s 𝓕 (𝟙 X) hfst hsnd n (ofSemilinear (𝟙 A) f) =
      ((cohomologyDeltaFunctor π).functor n).map
        ((tensorSheafFunctor π ((Scheme.Modules.pullback s).obj 𝓕)).map f) :=
  obstructionMapGen_id π s 𝓕 n hfst hsnd f (ofSemilinear (𝟙 A) f)
    (unit_comp_tensorSheafPullbackMapGen_id π s 𝓕 hfst hsnd f)

end Coefficient

end Deformation.Artin.SectionsSheaf

end
