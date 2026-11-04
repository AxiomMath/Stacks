module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel

/-!
# Sections over an open as morphisms out of the restricted structure sheaf

Let `X` be a scheme and `U` an open of `X`. The colimit statement of [Stacks, Tag 01YB]
identifies `colim_n Hom(I ^ n • G, F)` with `Hom_{𝒪_U}(G|_U, F|_U)` for `U = X ∖ V(I)`; this
file proves the part of that identification which is pure category theory and involves no ideal
sheaf at all: taking `G = 𝒪_X`, morphisms `𝒪_X|_U ⟶ M|_U` are the sections of `M` over `U`, and
such a morphism obtained by restricting some `φ : N ⟶ M` is read off by evaluating `φ` on a
section of `N` lying over `1`. That is what converts the morphism form of the tag into its
sections form.

## Main definitions

* `restrictSectionsEquiv`: global sections of `M|_U` are the sections of `M` over `U`.
* `unitRestrictHomEquiv`: `Hom_{𝒪_U}(𝒪_X|_U, M|_U) ≃ Γ(M, U)`.

## Main results

* `unitRestrictHomEquiv_eq_app`: the evaluation property of `unitRestrictHomEquiv`. If
  `ψ : 𝒪_X|_U ⟶ M|_U` restricts a morphism `φ : N ⟶ M` along some `j : N ⟶ 𝒪_X`, then the
  section of `M` over `U` that `ψ` corresponds to is `φ` applied to any section of `N` over `U`
  which `j` sends to `1`. This is what converts the morphism form of [Stacks, Tag 01YB] into
  its sections form, and with it the two sections assertions of that tag follow formally from
  the two morphism assertions.

## Implementation notes

The direct system `n ↦ I ^ n • M`, `n ↦ Hom(I ^ n • G, F)` and the open `X ∖ V(I)` are the
canonical ones, `Stacks.LocalCohomology.idealPowerSystem`,
`Stacks.LocalCohomology.idealPowerHom` and `Stacks.LocalCohomology.idealComplement` of
`StacksFrontier.AlgebraicGeometry.LocalCohomology.CanonicalSectionsMap`, on which the rest of the
library builds, including the map out of the colimit,
`Stacks.LocalCohomology.canonicalMapToHoms`.

`AlgebraicGeometry.Scheme.Modules` is a `def`, so `rw` fails its motive check on equalities of
morphisms transported to elements; every such step below goes through `congrArg` and `Eq.trans`
instead. The two identifications `Γ(M|_U, ⊤) = Γ(M, U.ι ''ᵁ ⊤)` and
`Γ(M.val, V) = Γ(M, V)` are definitional, but `U.ι ''ᵁ ⊤ = U` is not, so
`restrictSectionsEquiv` carries one transport along `AlgebraicGeometry.Scheme.Opens.ι_image_top`.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.IdealPowerHomColimit

variable {X : Scheme.{u}}

/-! ### Sections over an open as morphisms out of the restricted structure sheaf -/

/-- Global sections of the restriction of `M` to an open `U` are the sections of `M` over `U`. -/
public noncomputable def restrictSectionsEquiv (U : X.Opens) (M : X.Modules) :
    (M.restrict U.ι).sections ≃ Γ(M, U) :=
  (Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal
      (M.restrict U.ι) isTerminalTop).trans
    ((forget _).mapIso
      (M.presheaf.mapIso (eqToIso (congrArg op U.ι_image_top)))).toEquiv

/-- `restrictSectionsEquiv` sends a global section to its value at `⊤`, transported along
`U.ι ''ᵁ ⊤ = U`. -/
public lemma restrictSectionsEquiv_apply (U : X.Opens) (M : X.Modules)
    (s : (M.restrict U.ι).sections) :
    restrictSectionsEquiv U M s =
      M.presheaf.map (eqToHom (congrArg op U.ι_image_top)) (s.val (op ⊤)) := rfl

/-- Restricting a morphism to an open and then taking sections over `⊤` is taking sections
over the image of `⊤`. -/
public lemma restrictFunctor_map_val_app (U : X.Opens) {N M : X.Modules} (h : N ⟶ M)
    (V : U.toScheme.Opens) (x : Γ(N, U.ι ''ᵁ V)) :
    ((Scheme.Modules.restrictFunctor U.ι).map h).val.app (op V) x =
      h.val.app (op (U.ι ''ᵁ V)) x := rfl

/-- The inverse of `restrictUnitIso` preserves the unit section. -/
public lemma restrictUnitIso_inv_val_app_one (U : X.Opens) (V : U.toScheme.Opens) :
    (Scheme.Modules.restrictUnitIso U.ι).inv.val.app (op V) (1 : Γ(U.toScheme, V)) =
      (1 : Γ(X, U.ι ''ᵁ V)) := by
  have h : (U.ι.appIso V).hom (1 : Γ(X, U.ι ''ᵁ V)) = (1 : Γ(U.toScheme, V)) := by
    simp
  exact ((U.ι.appIso V).commRingCatIsoToRingEquiv.symm_apply_eq).mpr h.symm

/-- Morphisms from the restricted structure sheaf `𝒪_U` to `M|_U` are the sections of `M`
over `U`. -/
public noncomputable def unitRestrictHomEquiv (U : X.Opens) (M : X.Modules) :
    (Scheme.Modules.restrict (SheafOfModules.unit X.ringCatSheaf) U.ι ⟶ M.restrict U.ι) ≃
      Γ(M, U) :=
  ((Scheme.Modules.restrictUnitIso U.ι).homFromEquiv.trans
    (M.restrict U.ι).unitHomEquiv).trans (restrictSectionsEquiv U M)

/-- The evaluation property of `unitRestrictHomEquiv`.

If `ψ : 𝒪_U ⟶ M|_U` is obtained by restricting `φ : N ⟶ M` along a map `j : N ⟶ 𝒪_X`, then the
section of `M` over `U` attached to `ψ` is `φ` applied to any section of `N` over `U` that `j`
sends to `1`. This is the formal step that turns the morphism form of [Stacks, Tag 01YB] into
its sections form. -/
public lemma unitRestrictHomEquiv_eq_app (U : X.Opens) {N M : X.Modules}
    (j : N ⟶ SheafOfModules.unit X.ringCatSheaf) (φ : N ⟶ M)
    (ψ : Scheme.Modules.restrict (SheafOfModules.unit X.ringCatSheaf) U.ι ⟶ M.restrict U.ι)
    (s : Γ(N, U)) (hs : j.val.app (op U) s = (1 : Γ(X, U)))
    (key : (Scheme.Modules.restrictFunctor U.ι).map j ≫ ψ =
      (Scheme.Modules.restrictFunctor U.ι).map φ) :
    unitRestrictHomEquiv U M ψ = φ.val.app (op U) s := by
  -- `s` transported along `U.ι ''ᵁ ⊤ = U`
  set e : op U ⟶ op (U.ι ''ᵁ ⊤) := eqToHom (congrArg op U.ι_image_top.symm) with he
  set e' : op (U.ι ''ᵁ ⊤) ⟶ op U := eqToHom (congrArg op U.ι_image_top) with he'
  set s' : Γ(N, U.ι ''ᵁ ⊤) := N.val.map e s with hs'
  have hmid : ∀ y : M.val.obj (op U), M.val.map (𝟙 (op U)) y = y := by
    intro y
    rw [M.val.map_id]
    rfl
  -- the transported section still goes to `1`
  have hs1 : j.val.app (op (U.ι ''ᵁ ⊤)) s' = (1 : Γ(X, U.ι ''ᵁ ⊤)) :=
    (PresheafOfModules.naturality_apply j.val e s).trans
      ((congrArg (fun y => (SheafOfModules.unit X.ringCatSheaf).val.map e y) hs).trans
        (PresheafOfModules.unit_map_one _ _))
  have step1 : ((Scheme.Modules.restrictUnitIso U.ι).inv ≫ ψ).val.app (op ⊤)
      (1 : Γ(U.toScheme, ⊤)) = ψ.val.app (op ⊤) (1 : Γ(X, U.ι ''ᵁ ⊤)) :=
    congrArg (fun y => ψ.val.app (op ⊤) y) (restrictUnitIso_inv_val_app_one U ⊤)
  have step2 : ψ.val.app (op ⊤) (1 : Γ(X, U.ι ''ᵁ ⊤)) = φ.val.app (op (U.ι ''ᵁ ⊤)) s' :=
    (congrArg (fun y => ψ.val.app (op ⊤) y) hs1.symm).trans
      (congrArg (fun g : N.restrict U.ι ⟶ M.restrict U.ι => g.val.app (op ⊤) s') key)
  have hid : e ≫ e' = 𝟙 (op U) := by simp [he, he']
  have step3 : M.val.map e' (φ.val.app (op (U.ι ''ᵁ ⊤)) s') = φ.val.app (op U) s :=
    (congrArg (fun y => M.val.map e' y)
        (PresheafOfModules.naturality_apply φ.val e s)).trans
      ((PresheafOfModules.map_comp_apply M.val e e' (φ.val.app (op U) s)).symm.trans
        ((PresheafOfModules.congr_map_apply M.val hid _).trans (hmid _)))
  exact (congrArg (fun y => M.val.map e' y) step1).trans
    ((congrArg (fun y => M.val.map e' y) step2).trans step3)

end Stacks.AlgebraicGeometry.IdealPowerHomColimit

end
