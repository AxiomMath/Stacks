module

public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.PullbackInternalHomCompTwoIso

/-!
# Invertibility and cancellation in the composition law for internal Hom

Let `φ : X ⟶ Y` and `ψ : Y ⟶ Z` be morphisms of ringed topoi between the topoi of three ringed
sites, with their composite supplied as data `(χ, τ)`. From the composition law
`Stacks.SheafOfModules.InternalHom.toposPullbackInternalHomMap_compOf` for the canonical map
`χ^* Hom_{O_Z}(F, G) ⟶ Hom_{O_X}(χ^*F, χ^*G)` this file deduces how invertibility of the
canonical maps of `φ`, `ψ` and `χ` propagates.

## Main definitions

* `Stacks.SheafOfModules.InternalHom.toposCompositeComparisonOfTwoIso`: the comparison of direct
  images attached to a 2-isomorphism from the composite `ψ ∘ φ` to `χ`.

## Main results

* `Stacks.SheafOfModules.InternalHom.isIso_toposPullbackInternalHomMap_compOf`: if the canonical
  maps of `ψ` and of `φ` are isomorphisms, so is that of `χ`.
* `Stacks.SheafOfModules.InternalHom.isIso_map_toposPullbackInternalHomMap_of_compOf`: if the
  canonical maps of `χ` and of `φ` are isomorphisms, so is the pullback along `φ` of that of `ψ`.
* `Stacks.SheafOfModules.InternalHom.isIso_toposPullbackInternalHomMap_of_iso_first`: invertibility
  of the canonical map is invariant under an isomorphism in the first variable.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules (fSharpSet fSharpSetComp pullbackModulesCompIso)

namespace Stacks.SheafOfModules.InternalHom

universe u

variable {X Y Z : RingedSite.{u, u, u}}
  (φ : RingedToposHom (RingedSite.ringedTopos X) (RingedSite.ringedTopos Y))
  (ψ : RingedToposHom (RingedSite.ringedTopos Y) (RingedSite.ringedTopos Z))
  (χ : RingedToposHom (RingedSite.ringedTopos X) (RingedSite.ringedTopos Z))
  (τ : φ.toModulesHom.toToposHom.pushforward ⋙ ψ.toModulesHom.toToposHom.pushforward ≅
    χ.toModulesHom.toToposHom.pushforward)
  (hτ : fSharpSetComp φ.toModulesHom ψ.toModulesHom ≫ τ.hom.app _ =
    fSharpSet χ.toModulesHom)

/-- The comparison `χ^*A ⟶ φ^*ψ^*A` of pullbacks attached to `(χ, τ)` is an isomorphism. -/
instance isIso_toposPullbackCompComparisonOf
    (A : SheafOfModules.{u} (Tensor.ringSheaf Z.O)) :
    IsIso (toposPullbackCompComparisonOf φ ψ χ τ hτ A) :=
  inferInstanceAs (IsIso
    ((pullbackModulesCompIso φ.toModulesHom ψ.toModulesHom χ.toModulesHom τ hτ).hom.app A))

/-- The comparison `φ^*ψ^*A ⟶ χ^*A` of pullbacks attached to `(χ, τ)` is an isomorphism. -/
instance isIso_toposPullbackCompComparisonInvOf
    (A : SheafOfModules.{u} (Tensor.ringSheaf Z.O)) :
    IsIso (toposPullbackCompComparisonInvOf φ ψ χ τ hτ A) :=
  inferInstanceAs (IsIso
    ((pullbackModulesCompIso φ.toModulesHom ψ.toModulesHom χ.toModulesHom τ hτ).inv.app A))

variable (F G : SheafOfModules.{u} (Tensor.ringSheaf Z.O))

/-- The comparison `φ_* ⋙ ψ_* ≅ χ_*` of direct images attached to a 2-isomorphism `t` from the
composite `ψ ∘ φ` to `χ`. -/
def toposCompositeComparisonOfTwoIso
    (t : RingedToposHom.TwoIso (A := RingedSite.ringedTopos X)
      (B := RingedSite.ringedTopos Z)
      (RingedToposHom.comp (X := RingedSite.ringedTopos X)
        (Y := RingedSite.ringedTopos Y) (Z := RingedSite.ringedTopos Z) ψ φ) χ) :
    φ.toModulesHom.toToposHom.pushforward ⋙ ψ.toModulesHom.toToposHom.pushforward ≅
      χ.toModulesHom.toToposHom.pushforward :=
  RingedToposHom.toModulesHomPushforwardIso φ ψ ≪≫ t.e

/-- The comparison of direct images attached to a 2-isomorphism carries the composite structure
map of `ψ ∘ φ` to the structure map of `χ`. -/
theorem fSharpSet_toposCompositeComparisonOfTwoIso
    (t : RingedToposHom.TwoIso (A := RingedSite.ringedTopos X)
      (B := RingedSite.ringedTopos Z)
      (RingedToposHom.comp (X := RingedSite.ringedTopos X)
        (Y := RingedSite.ringedTopos Y) (Z := RingedSite.ringedTopos Z) ψ φ) χ) :
    fSharpSetComp φ.toModulesHom ψ.toModulesHom ≫
      (toposCompositeComparisonOfTwoIso φ ψ χ t).hom.app _ = fSharpSet χ.toModulesHom := by
  show fSharpSetComp φ.toModulesHom ψ.toModulesHom ≫
    ((RingedToposHom.toModulesHomPushforwardIso φ ψ).hom.app _ ≫ t.e.hom.app _) = _
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (fun m ↦ m ≫ t.e.hom.app _)
    (RingedToposHom.fSharpSetComp_toModulesHomPushforwardIso φ ψ)).trans t.commutes

include τ hτ in
/-- If the canonical map of `ψ` at `(F, G)` and the canonical map of `φ` at `(ψ^*F, ψ^*G)` are
isomorphisms, then so is the canonical map of `χ` at `(F, G)`. -/
theorem isIso_toposPullbackInternalHomMap_compOf
    (hψ : IsIso (toposPullbackInternalHomMap ψ F G))
    (hφ : IsIso (toposPullbackInternalHomMap φ
      ((toposPullback ψ).obj F) ((toposPullback ψ).obj G))) :
    IsIso (toposPullbackInternalHomMap χ F G) := by
  rw [toposPullbackInternalHomMap_compOf φ ψ χ τ hτ F G]
  infer_instance

include τ hτ in
/-- If the canonical map of `χ` at `(F, G)` and the canonical map of `φ` at `(ψ^*F, ψ^*G)` are
isomorphisms, then so is the pullback along `φ` of the canonical map of `ψ` at `(F, G)`. -/
theorem isIso_map_toposPullbackInternalHomMap_of_compOf
    (hχ : IsIso (toposPullbackInternalHomMap χ F G))
    (hφ : IsIso (toposPullbackInternalHomMap φ
      ((toposPullback ψ).obj F) ((toposPullback ψ).obj G))) :
    IsIso ((toposPullback φ).map (toposPullbackInternalHomMap ψ F G)) := by
  let s := toposPullbackInternalHomMap φ ((toposPullback ψ).obj F)
      ((toposPullback ψ).obj G) ≫
    (internalHomPre X.O (toposPullbackCompComparisonOf φ ψ χ τ hτ F)).app
        ((toposPullback φ).obj ((toposPullback ψ).obj G)) ≫
      (internalHomSecondFunctor X.J X.O ((toposPullback χ).obj F)).map
        (toposPullbackCompComparisonInvOf φ ψ χ τ hτ G)
  have : IsIso ((toposPullback φ).map (toposPullbackInternalHomMap ψ F G) ≫ s) :=
    IsIso.of_isIso_fac_left (toposPullbackInternalHomMap_compOf φ ψ χ τ hτ F G).symm
  exact IsIso.of_isIso_comp_right
    (g := (toposPullback φ).map (toposPullbackInternalHomMap ψ F G)) (f := s)

/-- If `A ≅ B` and the canonical map of `φ` at `(B, T)` is an isomorphism, then so is the
canonical map of `φ` at `(A, T)`. -/
theorem isIso_toposPullbackInternalHomMap_of_iso_first
    {A B : SheafOfModules.{u} (Tensor.ringSheaf Y.O)} (e : A ≅ B)
    (T : SheafOfModules.{u} (Tensor.ringSheaf Y.O))
    (hB : IsIso (toposPullbackInternalHomMap φ B T)) :
    IsIso (toposPullbackInternalHomMap φ A T) :=
  IsIso.of_isIso_fac_left (toposPullbackInternalHomMap_naturality φ T e.hom).symm

/-- If the functors `P` and `Q` are isomorphic and `P.map m` is an isomorphism, then so is
`Q.map m`. -/
theorem isIso_map_of_comparison {C D : Type*} [Category* C] [Category* D]
    {P Q : C ⥤ D} (e : P ≅ Q) {A B : C} (m : A ⟶ B) (h : IsIso (P.map m)) :
    IsIso (Q.map m) :=
  IsIso.of_isIso_fac_left (e.hom.naturality m).symm

end Stacks.SheafOfModules.InternalHom

end
