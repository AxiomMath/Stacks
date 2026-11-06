module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalars
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The sheaf `Hom_R(X, -)` of a bimodule

Let `R` and `Λ` be rings, not necessarily commutative, and let `X` be an `(R, Λ)`-bimodule: a
left `R`-module together with a right action of `Λ` by `R`-linear endomorphisms, recorded as a
ring morphism `ρ : Λ →+* (End_R X)ᵐᵒᵖ`. For an `R`-module `P`, the group `Hom_R(X, P)` is a left
`Λ`-module through `ρ`: `(λ f)(x) = f(x λ)`. This gives an additive functor
`Hom_R(X, -) : Mod(R) ⥤ Mod(Λ)` preserving limits, and hence, applied sectionwise, a functor from
sheaves of `R`-modules to sheaves of `Λ`-modules on the small étale site of a scheme.

## Main definitions

* `Stacks.EtaleCohomology.homFunctor`: the functor `Hom_R(X, -) : Mod(R) ⥤ Mod(Λ)`.
* `Stacks.EtaleCohomology.etaleModuleHom`: the same functor on sheaves of modules on the small
  étale site.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w u

namespace Stacks.EtaleCohomology

variable {R Λ : Type} [Ring R] [Ring Λ]

/-- **The functor `Hom_R(X, -) : Mod(R) ⥤ Mod(Λ)`** of an `(R, Λ)`-bimodule `X`, the right action
of `Λ` on `X` being given by `ρ : Λ →+* (End_R X)ᵐᵒᵖ`: the `Λ`-module structure on `Hom_R(X, P)`
is `(λ f)(x) = f(x λ)`. -/
@[sga "4 IV 11.1.3" "partial, special case"]
def homFunctor (X : ModuleCat.{w} R) (ρ : Λ →+* (End X)ᵐᵒᵖ) :
    ModuleCat.{w} R ⥤ ModuleCat.{w} Λ :=
  preadditiveCoyonedaObj X ⋙ ModuleCat.restrictScalars.{w} ρ

variable (X : ModuleCat.{w} R) (ρ : Λ →+* (End X)ᵐᵒᵖ)

instance homFunctor_additive : (homFunctor X ρ).Additive :=
  inferInstanceAs (preadditiveCoyonedaObj X ⋙ ModuleCat.restrictScalars.{w} ρ).Additive

lemma homFunctor_obj (P : ModuleCat.{w} R) :
    (homFunctor X ρ).obj P = (ModuleCat.restrictScalars.{w} ρ).obj (ModuleCat.of _ (X ⟶ P)) :=
  rfl

lemma homFunctor_smul_apply {P : ModuleCat.{w} R} (l : Λ) (f : (homFunctor X ρ).obj P) :
    (l • f : (homFunctor X ρ).obj P) = ((ρ l).unop.asHom ≫ (show X ⟶ P from f) : X ⟶ P) :=
  rfl

lemma homFunctor_map_apply {P Q : ModuleCat.{w} R} (g : P ⟶ Q) (f : (homFunctor X ρ).obj P) :
    (homFunctor X ρ).map g f = ((show X ⟶ P from f) ≫ g : X ⟶ Q) :=
  rfl

instance homFunctor_preservesLimits : PreservesLimits (homFunctor X ρ) := by
  have : PreservesLimits (ModuleCat.restrictScalars.{w} ρ) :=
    (Stacks.NoncommChangeOfRings.extendRestrictScalarsAdj.{w} ρ).rightAdjoint_preservesLimits
  exact comp_preservesLimits (preadditiveCoyonedaObj X) (ModuleCat.restrictScalars.{w} ρ)

/-- **The sheaf `Hom_R(X, -)`** on the small étale site of `U`: the functor `Hom_R(X, -)` applied
sectionwise to a sheaf of `R`-modules. -/
def etaleModuleHom (X : ModuleCat.{u + 1} R) (ρ : Λ →+* (End X)ᵐᵒᵖ) (U : Scheme.{u}) :
    EtaleModules.{u, 0} R U ⥤ EtaleModules.{u, 0} Λ U :=
  sheafCompose U.smallEtaleTopology (homFunctor X ρ)

instance etaleModuleHom_additive (X : ModuleCat.{u + 1} R) (ρ : Λ →+* (End X)ᵐᵒᵖ)
    (U : Scheme.{u}) : (etaleModuleHom X ρ U).Additive where
  map_add {F G f g} := by
    apply Sheaf.hom_ext
    ext W : 2
    exact (homFunctor X ρ).map_add

end Stacks.EtaleCohomology
