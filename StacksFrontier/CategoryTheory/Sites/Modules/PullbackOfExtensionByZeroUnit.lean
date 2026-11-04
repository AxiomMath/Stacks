module

public import StacksFrontier.CategoryTheory.Sites.Modules.SectionsOverObjectCorepresentable
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSiteHomOfRingedSite
import StacksCore.Tactic.StacksAttribute

/-!
# The inverse image of the extension by zero of the structure sheaf

Let `f : (C, O_C) ⟶ (D, O_D)` be a morphism of ringed sites given by the continuous functor
`u : D ⥤ C`, let `V` be an object of `D` and put `U = u(V)`. This file proves

`f^* (j_{V!} O_V) ≅ j_{U!} O_U`.

Both sides corepresent the same functor on `O_C`-modules, namely `Γ(U, -)`: the left-hand side
corepresents `Hom_{O_D}(j_{V!} O_V, f_* -) = Γ(V, f_* -)`, which is `Γ(U, -)` on the nose
because `f_*` is precomposition with `u.op`, and the right-hand side corepresents `Γ(U, -)`
directly. Since `CategoryTheory.preadditiveCoyoneda` is fully faithful, that is enough.

The transposition step is recorded separately as `CategoryTheory.Adjunction.coyonedaAddIso`:
for an adjunction `L ⊣ G` with `G` additive, the functor corepresented by `L X` is the functor
corepresented by `X` composed with `G`. Mathlib has the underlying bijection
(`CategoryTheory.Adjunction.homEquiv`) and its naturality, but not the statement that the
bijection is additive, which is what makes it an isomorphism of `AddCommGrpCat`-valued functors
and hence usable with the fully faithful `preadditiveCoyoneda`.

Together with the flatness of `j_{V!} O_V` (Stacks 03EV,
`AlgebraicGeometry.SheafOfModules.sheafExtensionUnit_isFlat`) this is what identifies
`Lf^* (j_{V!} O_V)` with `j_{U!} O_U` in the derived category, which is the geometric input of
the unrestricted Stacks 0D6H.

## Main definitions

* `CategoryTheory.Adjunction.coyonedaAddIso`: `Hom(L X, -) ≅ Hom(X, G -)` as an isomorphism of
  functors valued in abelian groups.
* `Stacks.Sites.ExtensionByZero.pullbackToposExtensionByZeroUnitIso`:
  `f^* (j_{V!} O_V) ≅ j_{U!} O_U`.

## References

* [Stacks Project, Tag 0G1V](https://stacks.math.columbia.edu/tag/0G1V)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03EV](https://stacks.math.columbia.edu/tag/03EV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.Cohomology.Localization

universe v u₁ u₂ u

namespace CategoryTheory.Adjunction

/-- **`Hom(L X, -) = Hom(X, G -)`, additively.** For an adjunction `L ⊣ G` between preadditive
categories with `G` additive, the functor corepresented by `L X` is the functor corepresented
by `X` composed with `G`.

Mathlib's `CategoryTheory.Adjunction.homEquiv` is the bijection and
`CategoryTheory.Adjunction.homEquiv_naturality_right` its naturality; what is added here is
additivity, which holds because transposition is composition with the unit followed by the
additive `G`. -/
noncomputable def coyonedaAddIso {A : Type u₁} [Category.{v} A] [Preadditive A] {B : Type u₂}
    [Category.{v} B] [Preadditive B] {L : A ⥤ B} {G : B ⥤ A} (adj : L ⊣ G) [G.Additive]
    (X : A) :
    preadditiveCoyoneda.obj (Opposite.op (L.obj X)) ≅ G ⋙ preadditiveCoyoneda.obj (Opposite.op X) :=
  NatIso.ofComponents
    (fun Z => (⟨adj.homEquiv X Z, fun f g => by
      simp only [Equiv.toFun_as_coe, Adjunction.homEquiv_unit, Functor.map_add,
        Preadditive.comp_add]⟩ : (L.obj X ⟶ Z) ≃+ (X ⟶ G.obj Z)).toAddCommGrpIso) (by
      intro Z Z' g
      ext h
      change adj.homEquiv X Z' (h ≫ g) = adj.homEquiv X Z h ≫ G.map g
      exact adj.homEquiv_naturality_right h g)

end CategoryTheory.Adjunction

namespace Stacks.Sites.ExtensionByZero

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y) (V : Y.C)
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] AlgebraicGeometry.RingedSite.Hom.pushforwardTopos_additive

/-- The functor corepresented by `f^* (j_{V!} O_V)` is `Γ(u V, -)`: transpose along
`f^* ⊣ f_*`, read `Hom(j_{V!} O_V, -)` as `Γ(V, -)` (Stacks 0G1V), and use that `Γ(V, f_* -)`
is `Γ(u V, -)` on the nose, `f_*` being precomposition with `u.op`. -/
noncomputable def coyonedaPullbackToposExtensionByZeroUnitIso :
    preadditiveCoyoneda.obj
        (op (f.toRingedToposSiteHom.pullbackTopos.obj
          (extensionByZeroUnitObj Y.J (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) V))) ≅
      sectionsOverObject X (f.u.obj V) :=
  (RingedToposSiteHom.pullbackPushforwardAdjunctionTopos
      f.toRingedToposSiteHom).coyonedaAddIso _ ≪≫
    Functor.isoWhiskerLeft f.toRingedToposSiteHom.pushforwardTopos
      (coyonedaExtensionByZeroUnitIso Y.J (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) V) ≪≫
    eqToIso rfl

/-- **The inverse image of the extension by zero of the structure sheaf.** For a morphism of
ringed sites `f` given by the continuous functor `u`, an object `V` of the target and
`U = u(V)`, the inverse image of `j_{V!} O_V` is `j_{U!} O_U`.

Both sides corepresent `Γ(U, -)` and `CategoryTheory.preadditiveCoyoneda` is fully faithful. -/
noncomputable def pullbackToposExtensionByZeroUnitIso :
    f.toRingedToposSiteHom.pullbackTopos.obj
        (extensionByZeroUnitObj Y.J (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) V) ≅
      extensionByZeroUnitObj X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (f.u.obj V) :=
  (preadditiveCoyoneda.preimageIso
    (coyonedaPullbackToposExtensionByZeroUnitIso f V ≪≫
      (coyonedaExtensionByZeroUnitIso X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (f.u.obj V)).symm)).unop.symm

end Stacks.Sites.ExtensionByZero

end
