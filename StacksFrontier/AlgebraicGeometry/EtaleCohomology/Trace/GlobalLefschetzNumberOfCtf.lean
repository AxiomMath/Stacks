module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalCompactSupportFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ShortExactTrace

/-!
# The global Lefschetz number of an object of `D_ctf(X, Λ)`

Let `Λ` be a finite ring, `X` a projective curve over a finite field `k` with `q = p ^ f`
elements, `k̄` an algebraic closure of `k` and `K ∈ D_ctf(X, Λ)`. The canonical map
`c_K : π_X^{-1} K ⟶ K` of [Stacks, Tag 03SR] base changes to `X_k̄ = X ×_k k̄` and induces an
action `π_X^*` on the perfect complex `RΓ(X_k̄, K|_{X_k̄})` ([Stacks, Tag 03TV]). The global
Lefschetz number of `K` is its trace, an element of `Λ^natural` ([Stacks, Tag 03TX]).

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleDirectImageCompGlobalSections` — `Γ(Y, g_* F) = Γ(X, F)`
  for `g : X ⟶ Y`, and its derived form
  `Stacks.EtaleCohomology.etaleModuleDerivedGlobalSectionsCompIso`,
  `RΓ(X, -) ≅ Rg_* ⋙ RΓ(Y, -)`.
* `Stacks.EtaleCohomology.fieldBaseChangeDerivedRestriction` — `K ↦ K|_{X_k̄}` on bounded
  below derived categories.
* `Stacks.EtaleCohomology.frobeniusBaseChangeDerivedMap` — the canonical morphism
  `K|_{X_k̄} ⟶ Rπ̄_*(K|_{X_k̄})`, natural in `K ∈ D⁺(X)`, where `π̄ = π_X × id`. It is the
  derived form of `Stacks.EtaleCohomology.frobeniusBaseChangeTwist`, the base change along
  `X_k̄ ⟶ X` of the Frobenius descent isomorphism `F ≅ (π_X)_* F` of [Stacks, Tag 03SR], i.e.
  the adjoint form of `c_K|_{X_k̄}`.
* `Stacks.EtaleCohomology.frobeniusGlobalSectionsEndo` — the action `π_X^*` on
  `RΓ(X_k̄, K|_{X_k̄})`.

## Main results

* `Stacks.EtaleCohomology.frobeniusBaseChangeDerivedMap_app_Qh` — on the class of a bounded
  below complex the canonical morphism is the degreewise base change twist followed by the unit
  of `Rπ̄_*`.
* `Stacks.EtaleCohomology.frobeniusGlobalSectionsEndo_naturality` — `π_X^*` is natural in `K`.

## References

* [Stacks Project, Tag 03TX](https://stacks.math.columbia.edu/tag/03TX)
* [Stacks Project, Tag 03TV](https://stacks.math.columbia.edu/tag/03TV)
* [Stacks Project, Tag 03SR](https://stacks.math.columbia.edu/tag/03SR)
* [Stacks Project, Tag 03SV](https://stacks.math.columbia.edu/tag/03SV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### Global sections of a direct image -/

section GlobalSections

variable (Λ : Type r) [Ring Λ]

/-- **Global sections of a direct image.** For `g : X ⟶ Y`, `Γ(Y, g_* F) = Γ(X, F)`: global
sections are sections over the final object, and base change along `g` carries the final object
of the small étale site of `Y` to a final object of that of `X`. -/
public def etaleModuleDirectImageCompGlobalSections {X Y : Scheme.{u}} (g : X ⟶ Y) :
    etaleModuleDirectImage.{u, r} Λ g ⋙ etaleModuleGlobalSections.{u, r} Λ Y ≅
      etaleModuleGlobalSections.{u, r} Λ X :=
  haveI : IsIso (Scheme.Etale.mk (𝟙 Y)).hom := inferInstanceAs (IsIso (𝟙 Y))
  haveI : IsIso (Scheme.Etale.mk (𝟙 X)).hom := inferInstanceAs (IsIso (𝟙 X))
  haveI : HasTerminal Y.Etale := (isTerminalOfIsIsoHom (Scheme.Etale.mk (𝟙 Y))).hasTerminal
  haveI : HasTerminal X.Etale := (isTerminalOfIsIsoHom (Scheme.Etale.mk (𝟙 X))).hasTerminal
  Functor.isoWhiskerLeft (etaleModuleDirectImage.{u, r} Λ g)
      (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)
        (isTerminalOfIsIsoHom (Scheme.Etale.mk (𝟙 Y)))) ≪≫
    NatIso.ofComponents (fun _ => Iso.refl _)
      (fun _ => by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]) ≪≫
    (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)
      (isTerminalSmallEtaleBaseChangeObj g
        (isTerminalOfIsIsoHom (Scheme.Etale.mk (𝟙 Y))))).symm

/-- **`RΓ(X, -) ≅ Rg_* ⋙ RΓ(Y, -)`** for `g : X ⟶ Y`: the composition comparison of the
derived functors of `Γ(Y, g_*(-)) = Γ(X, -)`, invertible because `g_*` preserves injective
sheaves. -/
public def etaleModuleDerivedGlobalSectionsCompIso {X Y : Scheme.{u}} (g : X ⟶ Y) :
    etaleModuleDerivedGlobalSections.{u, r} Λ X ≅
      etaleModuleDerivedDirectImage.{u, r} Λ g ⋙ etaleModuleDerivedGlobalSections.{u, r} Λ Y :=
  rightDerivedFunctorPlusCompIsoOfIso (etaleModuleDirectImage.{u, r} Λ g)
    (etaleModuleGlobalSections.{u, r} Λ Y) (etaleModuleGlobalSections.{u, r} Λ X)
    (etaleModuleDirectImageCompGlobalSections.{u, r} Λ g)

end GlobalSections

/-! ### The canonical morphism `K|_{X_k̄} ⟶ Rπ̄_*(K|_{X_k̄})` on `D⁺(X)` -/

section Frobenius

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- The restriction `K ↦ K|_{Y_k̄}` of a bounded below complex of sheaves of `Λ`-modules on
`Y_étale` to the base change `Y_k̄ = Y ×_k k̄`: the derived inverse image along the projection
`Y_k̄ ⟶ Y`, which is exact. -/
public abbrev fieldBaseChangeDerivedRestriction :
    DerivedCategory.Plus (EtaleModules.{u, r} Λ Y.left) ⥤
      DerivedCategory.Plus (EtaleModules.{u, r} Λ (fieldBaseChange Y kbar)) :=
  (etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapDerivedCategoryPlus

/-- The canonical morphism on bounded below homotopy categories: the base change twist
`Stacks.EtaleCohomology.frobeniusBaseChangeTwist` applied degreewise, followed by the unit of
the derived direct image along `π̄ = π_Y × id`. -/
public def frobeniusBaseChangeHomotopyMap :
    (etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ⟶
      ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh) ⋙
          etaleModuleDerivedDirectImage.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard) :=
  Functor.whiskerRight
      (Functor.mapHomotopyCategoryPlusNatTrans
          (frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard) ≫
        (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl _)).inv)
      DerivedCategory.Plus.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _
      (etaleModuleDirectImage.{u, r} Λ
        (geometricFrobeniusBaseChange Y kbar p q hcard)).rightDerivedFunctorPlusUnit ≫
    (Functor.associator _ _ _).inv

/-- **The canonical morphism `K|_{Y_k̄} ⟶ Rπ̄_*(K|_{Y_k̄})`**, natural in `K ∈ D⁺(Y_étale)`,
where `π̄ = π_Y × id` is the base change of the geometric Frobenius of [Stacks, Tag 03SQ]. It is
the derived form of the base change along `Y_k̄ ⟶ Y` of the Frobenius descent isomorphism
`F ≅ (π_Y)_* F` of [Stacks, Tag 03SR], that is, the adjoint form of the base change `c_K|_{Y_k̄}`
of the canonical map `c_K : π_Y^{-1} K ⟶ K`. It is obtained from
`Stacks.EtaleCohomology.frobeniusBaseChangeHomotopyMap` by the universal property of the
localization `K⁺(Y_étale) ⥤ D⁺(Y_étale)`. -/
public def frobeniusBaseChangeDerivedMap :
    fieldBaseChangeDerivedRestriction.{u, r} Λ Y kbar ⟶
      fieldBaseChangeDerivedRestriction.{u, r} Λ Y kbar ⋙
        etaleModuleDerivedDirectImage.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard) :=
  Localization.liftNatTrans DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso (EtaleModules.{u, r} Λ Y.left)) _ _ _ _
    (frobeniusBaseChangeHomotopyMap.{u, r} Λ Y kbar p q hcard)

/-- On the class of a bounded below complex the canonical morphism is computed by
`Stacks.EtaleCohomology.frobeniusBaseChangeHomotopyMap`, up to the identification of the derived
restriction with the degreewise one. -/
public theorem frobeniusBaseChangeDerivedMap_app_Qh
    (C : HomotopyCategory.Plus (EtaleModules.{u, r} Λ Y.left)) :
    (frobeniusBaseChangeDerivedMap.{u, r} Λ Y kbar p q hcard).app
        (DerivedCategory.Plus.Qh.obj C) =
      ((etaleModuleInverseImage.{u, r} Λ
          (fieldBaseChangeProj Y kbar)).mapDerivedCategoryPlusFactorsh.hom.app C) ≫
        (frobeniusBaseChangeHomotopyMap.{u, r} Λ Y kbar p q hcard).app C ≫
        (etaleModuleDerivedDirectImage.{u, r} Λ
          (geometricFrobeniusBaseChange Y kbar p q hcard)).map
          ((etaleModuleInverseImage.{u, r} Λ
            (fieldBaseChangeProj Y kbar)).mapDerivedCategoryPlusFactorsh.inv.app C) := by
  simp [frobeniusBaseChangeDerivedMap, Localization.liftNatTrans_app]
  rfl

/-- **The action `π_Y^*` on `RΓ(Y_k̄, K|_{Y_k̄})`** for `K ∈ D⁺(Y_étale)`: `RΓ(Y_k̄, -)` applied to
the canonical morphism `K|_{Y_k̄} ⟶ Rπ̄_*(K|_{Y_k̄})`, followed by
`RΓ(Y_k̄, Rπ̄_*(-)) ≅ RΓ(Y_k̄, -)`. This is the source's
`H^j(Y_k̄, K|) → H^j(Y_k̄, (π_Y^{-1}K)|) ≅ H^j(Y_k̄, K|)` of [Stacks, Tag 03SV] in adjoint form,
on the whole complex. -/
public def frobeniusGlobalSectionsEndo (K : DerivedCategory.Plus (EtaleModules.{u, r} Λ Y.left)) :
    (etaleModuleDerivedGlobalSections.{u, r} Λ (fieldBaseChange Y kbar)).obj
        ((fieldBaseChangeDerivedRestriction.{u, r} Λ Y kbar).obj K) ⟶
      (etaleModuleDerivedGlobalSections.{u, r} Λ (fieldBaseChange Y kbar)).obj
        ((fieldBaseChangeDerivedRestriction.{u, r} Λ Y kbar).obj K) :=
  (etaleModuleDerivedGlobalSections.{u, r} Λ (fieldBaseChange Y kbar)).map
      ((frobeniusBaseChangeDerivedMap.{u, r} Λ Y kbar p q hcard).app K) ≫
    (etaleModuleDerivedGlobalSectionsCompIso.{u, r} Λ
      (geometricFrobeniusBaseChange Y kbar p q hcard)).inv.app
        ((fieldBaseChangeDerivedRestriction.{u, r} Λ Y kbar).obj K)

/-- **`π_Y^*` is natural in `K`.** -/
public theorem frobeniusGlobalSectionsEndo_naturality
    {K L : DerivedCategory.Plus (EtaleModules.{u, r} Λ Y.left)} (φ : K ⟶ L) :
    (etaleModuleDerivedGlobalSections.{u, r} Λ (fieldBaseChange Y kbar)).map
        ((fieldBaseChangeDerivedRestriction.{u, r} Λ Y kbar).map φ) ≫
      frobeniusGlobalSectionsEndo.{u, r} Λ Y kbar p q hcard L =
    frobeniusGlobalSectionsEndo.{u, r} Λ Y kbar p q hcard K ≫
      (etaleModuleDerivedGlobalSections.{u, r} Λ (fieldBaseChange Y kbar)).map
        ((fieldBaseChangeDerivedRestriction.{u, r} Λ Y kbar).map φ) := by
  have h₁ := (frobeniusBaseChangeDerivedMap.{u, r} Λ Y kbar p q hcard).naturality φ
  have h₂ := (etaleModuleDerivedGlobalSectionsCompIso.{u, r} Λ
    (geometricFrobeniusBaseChange Y kbar p q hcard)).inv.naturality
      ((fieldBaseChangeDerivedRestriction.{u, r} Λ Y kbar).map φ)
  dsimp only [Functor.comp_map] at h₁ h₂
  simp only [frobeniusGlobalSectionsEndo, ← Category.assoc, ← Functor.map_comp, h₁]
  simp only [Functor.map_comp, Category.assoc, h₂]

end Frobenius

end Stacks.EtaleCohomology

end
