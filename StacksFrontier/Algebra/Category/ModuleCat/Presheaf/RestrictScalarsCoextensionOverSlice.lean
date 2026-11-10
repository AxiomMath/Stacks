module

public import Mathlib.CategoryTheory.Equivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.RestrictScalarsCoextension

/-!
# Coextension of scalars commutes with restriction to a slice

Let `φ : O ⟶ O'` be a morphism of presheaves of rings on `C`, let `F` be a presheaf of
`O`-modules, and let `U : C`. This file compares, over the slice `C / U`:

* restricting `coextendScalars φ` applied to `F` to `C / U`, against
* applying `coextendScalars` for the restricted ring morphism `φ|_U : O|_U ⟶ O'|_U` to the
  restricted module `F|_U`.

Concretely, writing `restrictToOver U` for restriction of a presheaf of modules to `Over U`
(pullback along `Over.forget U`) and `restrictPhi φ U` for `φ` restricted to `Over U`
(`Functor.whiskerLeft (Over.forget U).op φ`), the comparison is

`restrictToOver U (coextObj φ F) ≅ coextObj (restrictPhi φ U) (restrictToOver U F)`.

This does *not* follow from the Tag 0932 adjunction itself (which only concerns Hom-sets at a
fixed object), nor can it be read off from the analogous, near-trivial statement for
restriction of scalars (which is pure precomposition and commutes with slicing by `rfl`).
Unwinding `coextSec` at a section `w : Over U`, the two sides become a comparison between
`Hom` in `PresheafOfModules` over the *direct* slice `C / w.left` and `Hom` in
`PresheafOfModules` over the *iterated* slice `(C / U) / w`; these two slices are related by
Mathlib's equivalence `Over.iteratedSliceEquiv w : Over w ≌ Over w.left`, not by an equality of
categories, so the comparison is genuinely an isomorphism built from that equivalence, not a
`rfl`.

## Main results

* `Stacks.PresheafOfModules.CoextendScalars.coextOverSliceIso`: the comparison isomorphism
  `restrictToOver U (coextObj φ F) ≅ coextObj (restrictPhi φ U) (restrictToOver U F)` itself.
* `Stacks.PresheafOfModules.CoextendScalars.directIterEquiv`: at a fixed `w : Over U`, the
  bijection between `coextSec φ F (op w.left)` (direct slice) and
  `coextSec (restrictPhi φ U) (restrictToOver U F) (op w)` (iterated slice), built from the two
  pushforwards along the forward/backward functors of `Over.iteratedSliceEquiv w`.
* `Stacks.PresheafOfModules.CoextendScalars.coextSecDirectIterLinearEquiv`: the bijection,
  upgraded to an `O'(w.left)`-linear equivalence.
* `Stacks.PresheafOfModules.CoextendScalars.coextSecDirectIterEquiv_naturality`: the bijection is
  natural in `w : Over U`.

## Implementation notes

The construction rests on two facts about `Over.iteratedSliceEquiv w`, both by `rfl`:

* `Over.iteratedSliceBackward w ⋙ Over.iteratedSliceForward w = 𝟭 _` (only this direction of
  the equivalence's defining triangle is definitional; the other,
  `Over.iteratedSliceForward w ⋙ Over.iteratedSliceBackward w = 𝟭 _`, is not — it only holds up
  to the equivalence's nontrivial `unitIso`), and
* `PresheafOfModules.pushforward₀` turns functor composition into functor composition on the
  nose (`pushforward₀ F₁ R ⋙ pushforward₀ F₂ (F₁.op ⋙ R) = pushforward₀ (F₂ ⋙ F₁) R`, `rfl`).

Together these make `(pushforward₀ (Over.iteratedSliceBackward w) _).map` an *exact* (not just
up-to-iso) left inverse of `(pushforward₀ (Over.iteratedSliceForward w) _).map` on Homs. That
left inverse is also injective, because `Over.iteratedSliceForward w` is (part of) an
equivalence, hence so is `(Over.iteratedSliceForward w).op`, hence precomposition by it is
faithful (`CategoryTheory.Functor.whiskeringLeft`), hence so is
`PresheafOfModules.pushforward₀ (Over.iteratedSliceForward w) _` composed with the (always
faithful) forgetful functor `PresheafOfModules.toPresheaf`. An exact left inverse plus
injectivity of that inverse gives a two-sided inverse for free, without ever having to resolve
the non-definitional direction of the equivalence's triangle by hand.

The underlying-type bijection `directIterEquiv`, its `O'`-linearity (`coextSecDirectIterEquiv_add`,
`coextSecDirectIterEquiv_smul`), and its naturality in `w`
(`coextSecDirectIterEquiv_naturality`) are bundled sectionwise into a `LinearEquiv`
(`coextSecDirectIterLinearEquiv`), converted to a `ModuleCat` isomorphism by
`LinearEquiv.toModuleIso`, and assembled via `PresheafOfModules.isoMk` into the full comparison
isomorphism `coextOverSliceIso`.

## References

* [Stacks Project, Tag 0996](https://stacks.math.columbia.edu/tag/0996), Lemma 20.26.1 part (2).
-/

@[expose] public section

open CategoryTheory

universe u

namespace Stacks.PresheafOfModules.CoextendScalars

variable {C : Type u} [Category.{u} C] {O O' : Cᵒᵖ ⥤ RingCat.{u}}

/-- `φ` restricted to the slice `Over U`: the whiskering of `φ` along `Over.forget U`. This is
`φ|_U : O|_U ⟶ O'|_U`. -/
noncomputable def restrictPhi (φ : O ⟶ O') (U : C) :
    ((Over.forget U).op ⋙ O) ⟶ ((Over.forget U).op ⋙ O') :=
  Functor.whiskerLeft (Over.forget U).op φ

/-- `O'` as an `O`-module (via `φ`), restricted to `Over U`, agrees with `O'|_U` as an
`O|_U`-module (via `φ|_U`). Both sides unfold to the same pushforward of the same unit module,
so this holds by `rfl`. -/
theorem restrictToOver_O'asOModule (φ : O ⟶ O') (U : C) :
    restrictToOver U (O'asOModule φ) = O'asOModule (restrictPhi φ U) := rfl

/-- Restricting to `Over U` and then to the iterated slice `Over w` (for `w : Over U`) agrees
with restricting directly to the slice `Over w.left` and then pushing forward along
`Over.iteratedSliceForward w`. Both sides unfold (via `PresheafOfModules.pushforward₀`'s
composition law and Mathlib's `Over.iteratedSliceForward_forget`) to the pushforward of `F`
along one and the same functor `Over w ⥤ C`, so this holds by `rfl`. -/
theorem restrictToOver_restrictToOver (F : PresheafOfModules.{u} O) (U : C) (w : Over U) :
    restrictToOver w (restrictToOver U F) =
      (PresheafOfModules.pushforward₀ (Over.iteratedSliceForward w) _).obj
        (restrictToOver w.left F) := rfl

/-- `Over.iteratedSliceBackward w` is (part of) an equivalence of categories, namely the
inverse of `Over.iteratedSliceEquiv w`. -/
noncomputable instance isEquivalence_iteratedSliceBackward {U : C} (w : Over U) :
    (Over.iteratedSliceBackward w).IsEquivalence :=
  Equivalence.isEquivalence_inverse (Over.iteratedSliceEquiv w)

/-- Opposites of equivalences are equivalences, specialized to `Over.iteratedSliceBackward`, in
the form instance search needs for the faithfulness argument below. -/
noncomputable instance isEquivalence_iteratedSliceBackward_op {U : C} (w : Over U) :
    (Over.iteratedSliceBackward w).op.IsEquivalence := inferInstance

/-- If `G.op` is (part of) an equivalence, then `(PresheafOfModules.pushforward₀ G R).map` is
injective: precomposition by an equivalence is faithful
(`CategoryTheory.Functor.whiskeringLeft`), the forgetful functor
`PresheafOfModules.toPresheaf` is faithful, and the two commute with `pushforward₀` by `rfl`. -/
theorem pushforward₀_map_injective {D E : Type u} [Category.{u} D] [Category.{u} E]
    (G : D ⥤ E) [G.op.IsEquivalence] (R : Eᵒᵖ ⥤ RingCat.{u}) {M₁ M₂ : PresheafOfModules.{u} R}
    (h₁ h₂ : M₁ ⟶ M₂)
    (heq : (PresheafOfModules.pushforward₀ G R).map h₁ =
      (PresheafOfModules.pushforward₀ G R).map h₂) :
    h₁ = h₂ :=
  (PresheafOfModules.toPresheaf R).map_injective
    (((Functor.whiskeringLeft _ _ Ab).obj G.op).map_injective
      (congrArg (PresheafOfModules.toPresheaf _).map heq))

/-- **Fact B, underlying bijection.** At a fixed section `w : Over U`, the comparison between
`Hom` in `PresheafOfModules` over the direct slice `C / w.left` and `Hom` in
`PresheafOfModules` over the iterated slice `(C / U) / w`: pushing a direct-slice morphism
forward along `Over.iteratedSliceForward w` is a bijection onto the iterated-slice morphisms,
with inverse given by pushing forward along `Over.iteratedSliceBackward w`.

This is the Hom-set content of comparing `restrictToOver U (coextObj φ F)` with
`coextObj (restrictPhi φ U) (restrictToOver U F)` sectionwise at `w`, via
`restrictToOver_O'asOModule` and `restrictToOver_restrictToOver`. -/
noncomputable def directIterEquiv {U : C} (w : Over U) {R' : (Over w.left)ᵒᵖ ⥤ RingCat.{u}}
    (M₁ M₂ : PresheafOfModules.{u} R') :
    (M₁ ⟶ M₂) ≃
      ((PresheafOfModules.pushforward₀ (Over.iteratedSliceForward w) R').obj M₁ ⟶
        (PresheafOfModules.pushforward₀ (Over.iteratedSliceForward w) R').obj M₂) where
  toFun h := (PresheafOfModules.pushforward₀ (Over.iteratedSliceForward w) R').map h
  invFun h := (PresheafOfModules.pushforward₀ (Over.iteratedSliceBackward w) _).map h
  left_inv _ := rfl
  right_inv _ := pushforward₀_map_injective (Over.iteratedSliceBackward w) _ _ _ rfl

/-- **Fact B, Hom-set form.** The bijection of `directIterEquiv`, transported along
`restrictToOver_O'asOModule` and `restrictToOver_restrictToOver` to compare, at a fixed
`w : Over U`, the internal-hom section `coextSec φ F` at `w.left` (direct slice) with the
internal-hom section `coextSec (restrictPhi φ U) (restrictToOver U F)` at `w` (iterated
slice). -/
noncomputable def coextSecDirectIterEquiv (φ : O ⟶ O') (F : PresheafOfModules.{u} O) (U : C)
    (w : Over U) :
    coextSec φ F (Opposite.op w.left) ≃
      coextSec (restrictPhi φ U) (restrictToOver U F) (Opposite.op w) :=
  directIterEquiv w (restrictToOver w.left (O'asOModule φ)) (restrictToOver w.left F)

/-- Pushing the right-multiplication endomorphism (by `a'`) forward along
`Over.iteratedSliceForward w` gives the right-multiplication endomorphism for the restricted
ring `O'|_U` at `w`. Both sides are, after unfolding, the same reindexing of the same
`AddMonoidHom.mulRight` data along the same functor on `Over w`, by `restrictToOver_O'asOModule`
and `Over.iteratedSliceForward_forget`, so this holds by `rfl`. -/
theorem directIterEquiv_rightMulEndo (φ : O ⟶ O') (U : C) (w : Over U)
    (a' : (O'.obj (Opposite.op w.left) : Type _)) :
    (PresheafOfModules.pushforward₀ (Over.iteratedSliceForward w) _).map
        (rightMulEndo φ w.left a') =
      rightMulEndo (restrictPhi φ U) w a' := rfl

/-- **Fact B, `O'`-linearity.** The bijection `coextSecDirectIterEquiv` is `O'(w.left)`-linear
for the coextension module action: transporting the direct-slice section `a' • ψ`
(`coextSMul`'s `rightMulEndo φ w.left a' ≫ ψ`, unfolded here to avoid an unrelated instance-
elaboration issue with the `•` notation at a non-variable index `Opposite.op w.left`) to the
iterated slice agrees with acting by `a'` on the transported section. -/
theorem coextSecDirectIterEquiv_smul (φ : O ⟶ O') (F : PresheafOfModules.{u} O) (U : C)
    (w : Over U) (a' : (O'.obj (Opposite.op w.left) : Type _))
    (ψ : coextSec φ F (Opposite.op w.left)) :
    coextSecDirectIterEquiv φ F U w (rightMulEndo φ w.left a' ≫ ψ) =
      rightMulEndo (restrictPhi φ U) w a' ≫ coextSecDirectIterEquiv φ F U w ψ :=
  (PresheafOfModules.pushforward₀ (Over.iteratedSliceForward w) _).map_comp _ _

/-- Restricting to the slice `C / w.left` and then pushing forward along the iterated-slice
comparison `Over.iteratedSliceForward w'` is the same functor as pushing forward along
`overRestrictFunctor w'.left w.left g.left` first and then restricting to `C / w'.left`: both
sides are reindexings of the same ring-change data along one and the same composite functor on
`Over w'`, so (unlike the rest of this file) this holds by `rfl`, with no appeal to
`Over.iteratedSliceEquiv` needed. -/
theorem overRestrictFunctor_comp_pushforward₀ {U : C} (w w' : Over U) (g : w' ⟶ w) :
    overRestrictFunctor w'.left w.left g.left ⋙
        PresheafOfModules.pushforward₀ (Over.iteratedSliceForward w') _ =
      PresheafOfModules.pushforward₀ (Over.iteratedSliceForward w) _ ⋙
        @overRestrictFunctor (Over U) _ ((Over.forget U).op ⋙ O) w' w g := rfl

/-- **Fact B, naturality in `w`.** The bijection `coextSecDirectIterEquiv` is natural in
`w : Over U`: transporting the direct-slice restriction map `coextRestrFun φ F g.left.op`
(restriction along `g.left : w'.left ⟶ w.left` in `C`) agrees with restricting along
`g : w' ⟶ w` in `Over U` after transporting.

The proof follows the one-category template of `coextMap_comp` (`coextRestrFun`'s own
functoriality) up to unfolding `coextRestrFun` and peeling the `overRestrictIso` conjugations,
but departs from it at the point where that template reaches for `conj_eqToHom_iff_heq`: here the
two sides of the naturality square live over *different* presentations of the same modules
(`restrictToOver w' (restrictToOver U M)` versus `(pushforward₀ (iteratedSliceForward w')).obj
(restrictToOver w'.left M)`, identified only by the non-syntactic `rfl` fact
`restrictToOver_restrictToOver`), and `rw`/`simp`'s congruence-closure for
`eqToHom_comp_iff`/`comp_eqToHom_iff` cannot see through that identification at reduced
transparency. Peeling the conjugating `eqToHom`s one at a time via the unconditional HEq lemmas
`eqToHom_comp_heq`/`comp_eqToHom_heq` (plain term-mode `HEq.trans`, not `rw`) sidesteps the wall,
and the resulting pointwise comparison of the two `overRestrictFunctor.map ψ` then closes by
`rfl` via `overRestrictFunctor_comp_pushforward₀`. -/
theorem coextSecDirectIterEquiv_naturality (φ : O ⟶ O') (F : PresheafOfModules.{u} O) {U : C}
    (w w' : Over U) (g : w' ⟶ w) (ψ : coextSec φ F (Opposite.op w.left)) :
    coextSecDirectIterEquiv φ F U w' (coextRestrFun φ F g.left.op ψ) =
      coextRestrFun (restrictPhi φ U) (restrictToOver U F) g.op
        (coextSecDirectIterEquiv φ F U w ψ) := by
  simp only [coextRestrFun]
  change (PresheafOfModules.pushforward₀ (Over.iteratedSliceForward w') _).map
      ((overRestrictIso w'.left w.left g.left (O'asOModule φ)).inv ≫
        (overRestrictFunctor w'.left w.left g.left).map ψ ≫
          (overRestrictIso w'.left w.left g.left F).hom) =
    (overRestrictIso w' w g (O'asOModule (restrictPhi φ U))).inv ≫
      (overRestrictFunctor w' w g).map ((coextSecDirectIterEquiv φ F U w) ψ) ≫
        (overRestrictIso w' w g (restrictToOver U F)).hom
  rw [Functor.map_comp, Functor.map_comp]
  simp only [overRestrictIso, eqToIso.inv, eqToIso.hom, eqToHom_map]
  apply eq_of_heq
  refine HEq.trans ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)) ?_
  refine HEq.trans ?_ ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).symm
  rfl

/-- **Fact B, additivity.** The bijection `coextSecDirectIterEquiv` is additive: it is
`(pushforward₀ (Over.iteratedSliceForward w) _).map` under the hood, and that map between the
underlying `PresheafOfModules.Hom` additive groups is additive on the nose, so this holds by
`rfl`. Together with `coextSecDirectIterEquiv_smul`, this upgrades `coextSecDirectIterEquiv` to
an `O'(w.left)`-linear equivalence. -/
theorem coextSecDirectIterEquiv_add (φ : O ⟶ O') (F : PresheafOfModules.{u} O) (U : C)
    (w : Over U) (ψ₁ ψ₂ : coextSec φ F (Opposite.op w.left)) :
    coextSecDirectIterEquiv φ F U w (ψ₁ + ψ₂) =
      coextSecDirectIterEquiv φ F U w ψ₁ + coextSecDirectIterEquiv φ F U w ψ₂ := rfl

/-- **Fact B, linear equivalence.** `coextSecDirectIterEquiv`, upgraded to an
`O'(w.left)`-linear equivalence using `coextSecDirectIterEquiv_add` and
`coextSecDirectIterEquiv_smul`. -/
noncomputable def coextSecDirectIterLinearEquiv (φ : O ⟶ O') (F : PresheafOfModules.{u} O)
    (U : C) (w : Over U) :
    coextObjModule φ F (Opposite.op w.left) ≃ₗ[O'.obj (Opposite.op w.left)]
      coextObjModule (restrictPhi φ U) (restrictToOver U F) (Opposite.op w) :=
  { coextSecDirectIterEquiv φ F U w with
    map_add' := coextSecDirectIterEquiv_add φ F U w
    map_smul' := coextSecDirectIterEquiv_smul φ F U w }

/-- **Fact B.** Coextension of scalars commutes with restriction to the slice site `Over U`:
restricting `coextendScalars φ F` to `C / U` agrees with coextending along `φ|_U` applied to
`F|_U`. Assembled, via `PresheafOfModules.isoMk`, from the sectionwise linear equivalence
`coextSecDirectIterLinearEquiv` (converted to a `ModuleCat` isomorphism by
`LinearEquiv.toModuleIso`) together with its naturality `coextSecDirectIterEquiv_naturality`. -/
noncomputable def coextOverSliceIso (φ : O ⟶ O') (F : PresheafOfModules.{u} O) (U : C) :
    restrictToOver U (coextObj φ F) ≅ coextObj (restrictPhi φ U) (restrictToOver U F) :=
  PresheafOfModules.isoMk
    (fun X => (coextSecDirectIterLinearEquiv φ F U X.unop).toModuleIso)
    (fun X Y f => by
      ext ψ
      change coextSecDirectIterEquiv φ F U Y.unop (coextRestrFun φ F f.unop.left.op ψ) =
        coextRestrFun (restrictPhi φ U) (restrictToOver U F) f.unop.op
          (coextSecDirectIterEquiv φ F U X.unop ψ)
      exact coextSecDirectIterEquiv_naturality φ F X.unop Y.unop f.unop ψ)

end Stacks.PresheafOfModules.CoextendScalars
