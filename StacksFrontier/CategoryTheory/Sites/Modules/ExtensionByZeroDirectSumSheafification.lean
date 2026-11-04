module

public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroExactness
import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero on a ringed site: the adjunction and the direct-sum formula

Let `(C, O)` be a ringed site and let `U` be an object of `C`. Restriction of sheaves of
`O`-modules to the localized site `C/U` is `j_U^*`, and Stacks 03DI asserts two things about
it: that it has a left adjoint `j_{U!}`, so that

`Mor_{Mod(O_U)}(G, j_U^* F) = Mor_{Mod(O)}(j_{U!} G, F)`,

and that `j_{U!} G` is the sheaf associated to the presheaf

`V ↦ ⨁_{φ ∈ Mor_C(V, U)} G(V →φ U)`.

Both are stated here outright, with no adjointness hypothesis. Existence is the instance
`Stacks.Sites.ExtensionByZero.sheafRestrictionIsRightAdjoint`, which is what makes Mathlib's
`SheafOfModules.pullback` — the functor Mathlib defines only *when* a left adjoint exists —
denote `j_{U!}` unconditionally here; the displayed bijection is its adjunction's transpose. The
direct-sum presheaf is `Stacks.Sites.ExtensionByZero.directSumPresheaf`, whose sections over `V`
are the displayed direct sum by `Stacks.Sites.ExtensionByZero.directSumPresheaf_obj`, and whose
identification with the presheaf Mathlib sheafifies is
`Stacks.Sites.ExtensionByZero.directSumPresheafIso`.

## Main definitions

* `Stacks.Sites.ExtensionByZero.extensionByZeroHomEquiv`: the displayed bijection of Stacks
  03DI, in the source's orientation.
* `Stacks.Sites.ExtensionByZero.extensionByZeroIsoSheafifyDirectSum`: `j_{U!} G` is the sheaf
  associated to the direct-sum presheaf.

## Implementation notes

No new functor is introduced: `j_{U!}` is Mathlib's `SheafOfModules.pullback` for
`Over.forget U` together with the identity map of the restricted sheaf of rings, which is the
spelling the rest of the development uses.

Mathlib's `SheafOfModules.pullbackIso` asks for the presheaf-level adjointness instance at a
spelling its discrimination tree does not match against
`Stacks.Sites.ExtensionByZero.presheafRestrictionIsRightAdjoint`, so that instance is put into
the local context by hand; unification against a local hypothesis succeeds where instance search
does not.

## References

* [Stacks Project, Tag 03DI](https://stacks.math.columbia.edu/tag/03DI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sites.ExtensionByZero

universe u

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  (R : Sheaf J RingCat.{u}) (U : C)
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

add_to_stacks 03DI "restriction to C/U has a left adjoint"
  Stacks.Sites.ExtensionByZero.sheafRestrictionIsRightAdjoint

/-- **Stacks 03DI**, the displayed bijection: morphisms of sheaves of `O_U`-modules
`G ⟶ j_U^* F` correspond to morphisms of sheaves of `O`-modules `j_{U!} G ⟶ F`.

This is the transpose of the adjunction `j_{U!} ⊣ j_U^*`, which is available with no
adjointness hypothesis because `sheafRestrictionIsRightAdjoint` discharges it. -/
@[stacks 03DI "Mor(G, j_U^* F) = Mor(j_{U!} G, F)"]
noncomputable def extensionByZeroHomEquiv (G : SheafOfModules.{u} (R.over U))
    (F : SheafOfModules.{u} R) :
    (G ⟶ (SheafOfModules.pushforward.{u} (F := Over.forget U)
        (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).obj F) ≃
      ((SheafOfModules.pullback.{u} (F := Over.forget U)
        (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).obj G ⟶ F) :=
  ((SheafOfModules.pullbackPushforwardAdjunction.{u}
    (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).homEquiv G F).symm

/-- `extensionByZeroHomEquiv` is composition with the unit of the adjunction: the morphism of
`O_U`-modules attached to `β : j_{U!} G ⟶ F` is `j_U^* β` precomposed with
`G ⟶ j_U^* j_{U!} G`. -/
lemma extensionByZeroHomEquiv_symm_apply (G : SheafOfModules.{u} (R.over U))
    (F : SheafOfModules.{u} R)
    (β : (SheafOfModules.pullback.{u} (F := Over.forget U)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).obj G ⟶ F) :
    (extensionByZeroHomEquiv J R U G F).symm β =
      (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).unit.app G ≫
        (SheafOfModules.pushforward.{u} (F := Over.forget U)
          (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).map β :=
  (SheafOfModules.pullbackPushforwardAdjunction.{u}
    (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).homEquiv_unit G F β

/-- **Stacks 03DI**, the direct-sum formula: the extension by zero `j_{U!} G` of a sheaf of
`O_U`-modules `G` is the sheaf associated to the presheaf whose sections over `V` are
`⨁_{φ ∈ Mor_C(V, U)} G(V →φ U)`.

That presheaf is `directSumPresheaf U R.obj G.val`; its sections over `V` are the displayed
direct sum by `directSumPresheaf_obj`, and its restriction maps are the restriction maps of `G`
between the summands by `presheafRestriction_ι_apply`. -/
@[stacks 03DI "j_{U!} G is the sheaf associated to V ↦ ⨁_{φ : V ⟶ U} G(φ)"]
noncomputable def extensionByZeroIsoSheafifyDirectSum (G : SheafOfModules.{u} (R.over U)) :
    (SheafOfModules.pullback.{u} (F := Over.forget U)
        (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).obj G ≅
      (PresheafOfModules.sheafification (R₀ := R.obj) (𝟙 R.obj)).obj
        (directSumPresheaf U R.obj G.val) :=
  have := presheafRestrictionIsRightAdjoint J R U
  (SheafOfModules.pullbackIso.{u}
      (φ := (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)))).app G ≪≫
    (PresheafOfModules.sheafification (R₀ := R.obj) (𝟙 R.obj)).mapIso
      (directSumPresheafIso U R.obj G.val).symm

end Stacks.Sites.ExtensionByZero
