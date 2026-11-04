module

public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.DualBaseChangeCompatibility
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleBaseChange
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.TopoiBridge.Basic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionToClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.TopSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Module maps into the structure sheaf, and the infinitesimal neighbourhoods

Let `κ : Z' ⟶ Z` be a closed immersion and `N` a finite locally free `𝒪_Z`-module. The morphisms
`N ⟶ 𝒪_Z` are the global sections of the dual `N^∨`, and the morphisms
`N ⟶ (ι_n) _* 𝒪_{Z'_n}` into the direct image from the `n`-th infinitesimal neighbourhood are the
sections of `N^∨` over that neighbourhood, because the dual base-change map
`ι_n^*(N^∨) ⟶ (ι_n^* N)^∨` of [Stacks, Tag 0GMX] is invertible for a finite locally free module.
This file builds those two identifications and shows that they carry the canonical maps between
the sections to composition with the canonical maps of direct image algebras.

## Main definitions

* `Stacks.FundamentalGroup.dualSectionsHom` — the morphisms `N ⟶ 𝒪_Z` are the global sections
  of `N^∨`.
* `Stacks.FundamentalGroup.pullbackDualSheafIso` — the dual base-change isomorphism
  `g^*(N^∨) ≅ (g^* N)^∨` of a finite locally free module, at Mathlib's pullback spelling.
* `Stacks.FundamentalGroup.dualNeighborhoodEquiv` — the sections of `g^*(N^∨)` over the source
  of `g` are the morphisms `N ⟶ g_* 𝒪`; for `g = ι_n` these are the morphisms
  `N ⟶ (ι_n) _* 𝒪_{Z'_n}`.
* `Stacks.FundamentalGroup.nthOrderTransitionMapLE` — the map of direct image algebras between
  two infinitesimal neighbourhoods `Z'_n ⊆ Z'_m`, of which
  `Stacks.FundamentalGroup.nthOrderTransitionMap` is the successor case.

## Main results

* `Stacks.FundamentalGroup.nthOrderUnitMap_eq_unit` — the canonical map
  `𝒪_Z ⟶ (ι_n) _* 𝒪_{Z'_n}` is the adjoint of the structure-sheaf comparison
  `ι_n^* 𝒪_Z ⟶ 𝒪_{Z'_n}`.
* `Stacks.FundamentalGroup.dualSectionsHom_pullbackGlobalSections` — the unit square: restricting
  a global section of `N^∨` to a neighbourhood corresponds to composing the morphism it names with
  the canonical map `𝒪_Z ⟶ (ι_n) _* 𝒪_{Z'_n}`.
* `Stacks.FundamentalGroup.nthOrderUnitMap_comp_nthOrderTransitionMapLE` and
  `Stacks.FundamentalGroup.transitionMapLE_compatible` — the canonical maps of the tower are
  compatible with its transition maps, and successor compatibility of a family of morphisms
  upgrades to compatibility for all `n ≤ m`.
* `Stacks.FundamentalGroup.pullbackDualMap_over` and
  `Stacks.FundamentalGroup.dualNeighborhoodEquiv_pullbackSectionsMap` — the transition square:
  the canonical map between the sections of `N^∨` over two schemes over `Z` corresponds under
  `Stacks.FundamentalGroup.dualNeighborhoodEquiv` to composition with the canonical map of
  direct image algebras.
* `Stacks.FundamentalGroup.nthOrderUnitMap_jointly_injective` and
  `Stacks.FundamentalGroup.exists_hom_of_nthOrderUnitMap_compatible` — the two clauses of
  `Stacks.FundamentalGroup.DualSectionsHypothesis`, for a finite locally free module whose dual
  has complete global sections: the canonical maps of the tower are jointly injective on the
  morphisms out of it, and every compatible family of morphisms into the direct image algebras
  comes from a morphism `N ⟶ 𝒪_Z`.

## Implementation notes

The dual base-change map is stated in the ringed-space spelling
`RingedSpaceModuleAdjunction.modulePullback g.toLRSHom.toShHom`, which is definitionally
`AlgebraicGeometry.Scheme.Modules.pullback g` but is not interchangeable with it to the
elaborator; `Stacks.ToposBridge.scheme_modules_pullback_eq` and
`Stacks.ModuleSkyscraper.pullbackPushforwardAdjunction_eq_modulePullbackPushforwardAdjunction`
are the named transports.

The unit square and the transition square are proved on components, and the components are taken
on `N` rather than on its pullback: a morphism `N ⟶ (ι_n) _* 𝒪_{Z'_n}` is, by
`CategoryTheory.Adjunction.homEquiv_unit`, determined by its values on the canonical images of
local sections of `N`, and on exactly those images the dual base-change map is computed by
`Stacks.Chow.pullbackDualMap_eval` together with `Stacks.Chow.pullbackEvaluation_unit_tmul`.
Taking the components on the pullback instead would need the much more expensive statement that
two morphisms out of `ι_n^* N` agreeing on canonical images agree.

In the transition square the section fed to the dual base-change map of the structure morphism of
the source is *not* a canonical image — it is the canonical map on sections applied to an
arbitrary section — so `Stacks.FundamentalGroup.pullbackDualSheafIso_unit_apply` does not reach
it. `Stacks.Chow.pullbackDualMap_comp` does: it is an identity of morphisms, hence holds of every
local section, and it factors the dual base-change map of the composite through the dual
base-change maps of the two factors, after which the section *is* a canonical image for the
second factor. The identification of the structure morphism of the source with that composite is
made by substituting it away, which is why the statement takes the identification as a hypothesis
rather than reading it off a morphism in the slice category.

The transition maps are given for an arbitrary `n ≤ m` rather than only for successors, because
that is the indexing of the compatible families of
`Stacks.Algebraization.IsInfinitesimalSectionsComplete`, while
`Stacks.FundamentalGroup.nthOrderTransitionMap` is the successor case alone.

## References

* [Stacks Project, Tag 0GN2](https://stacks.math.columbia.edu/tag/0GN2)
* [Stacks Project, Tag 0GMX](https://stacks.math.columbia.edu/tag/0GMX)
* [Stacks Project, Tag 0882](https://stacks.math.columbia.edu/tag/0882)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf dualPairing dualMap
  dualPairing_terminal dualMap_id)
open Stacks.Algebraization (nthInfinitesimalNeighbourhood nthInfinitesimalNeighbourhoodι
  nthInfinitesimalNeighbourhoodOver nthInfinitesimalNeighbourhoodTransition
  internalHomSectionsTopEquiv internalHomSectionsTopMapAddEquiv)
open Stacks.RelativeSpec Stacks.Thickenings
open scoped AlgebraicGeometry

universe u

namespace Stacks.FundamentalGroup

attribute [local instance] CategoryTheory.Abelian.toPreadditive

/-! ### Global sections of the dual -/

/-- **The global sections of the dual of `N` are the morphisms `N ⟶ 𝒪_X`.** This is the
degenerate case `U = ⊤` of the comparison of [Stacks, Tag 0882]. -/
public def dualSectionsHom {X : Scheme.{u}} (N : X.Modules) :
    (N ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) ≃ Γ(dualSheaf N, (⊤ : X.Opens)) :=
  ((Stacks.Algebraization.overFunctorTopFullyFaithful X).comp
    (SheafOfModules.fullyFaithfulForget _)).homEquiv

/-- **The component formula.** The section of `N^∨` attached to a morphism `N ⟶ 𝒪_X` evaluates,
at an object `W` of the slice site over the whole space, to the component of that morphism at the
underlying open. -/
public theorem dualSectionsHom_app {X : Scheme.{u}} (N : X.Modules)
    (φ : N ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) (W : Over (⊤ : X.Opens)) :
    (dualSectionsHom N φ).app (op W) = φ.val.app (op W.left) := rfl

/-- The morphism attached to a global section of `N^∨` has, at the open underlying `W`, the
component that the section has at `W`. -/
public theorem dualSectionsHom_symm_app {X : Scheme.{u}} (N : X.Modules)
    (s : Γ(dualSheaf N, (⊤ : X.Opens))) (W : Over (⊤ : X.Opens)) :
    ((dualSectionsHom N).symm s).val.app (op W.left) = s.app (op W) :=
  (dualSectionsHom_app N ((dualSectionsHom N).symm s) W).symm.trans
    (congrArg (fun t : Γ(dualSheaf N, (⊤ : X.Opens)) => t.app (op W))
      ((dualSectionsHom N).apply_symm_apply s))

/-! ### The dual base-change isomorphism at Mathlib's pullback -/

/-- **The dual base-change map of a finite locally free module is invertible**,
`g^*(N^∨) ≅ (g^* N)^∨`, written at `AlgebraicGeometry.Scheme.Modules.pullback`. -/
@[ega "0 5.4.5" "special case", ega "IV 18.5.1" "partial"]
public def pullbackDualSheafIso {X Y : Scheme.{u}} (g : Y ⟶ X) (N : X.Modules)
    (hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N) :
    (Scheme.Modules.pullback g).obj (dualSheaf N) ≅
      dualSheaf ((Scheme.Modules.pullback g).obj N) :=
  @asIso _ _ _ _ (Stacks.Chow.pullbackDualMap g N) (Stacks.Chow.pullbackDualMap_isIso g N hN)

/-- The dual base-change map, evaluated on the canonical image of a local functional, is the
pullback of the function that functional computes. -/
public theorem pullbackDualSheafIso_unit_apply {X Y : Scheme.{u}} (g : Y ⟶ X) (N : X.Modules)
    (hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N) (U : X.Opens)
    (s : (dualSheaf N).val.obj (op U)) (m : N.val.obj (op U)) :
    (((pullbackDualSheafIso g N hN).hom.val.app (op (g ⁻¹ᵁ U))
            (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
              (dualSheaf N)).val.app (op U) s)).app
          (op (Over.mk (𝟙 (g ⁻¹ᵁ U))))).hom
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).val.app (op U) m) =
      (g.app U).hom ((s.app (op (Over.mk (𝟙 U)))).hom m) :=
  (Stacks.Chow.pullbackDualMap_eval g N (g ⁻¹ᵁ U) _ _).trans
    (Stacks.Chow.pullbackEvaluation_unit_tmul g N U s m)

/-- **The dual base-change maps of two equal morphisms agree**, modulo the comparison
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` of their pullback functors on the source and
on the module being dualised. -/
public theorem pullbackDualMap_congr {X Y : Scheme.{u}} {f g : Y ⟶ X} (e : f = g)
    (N : X.Modules) :
    (Scheme.Modules.pullbackCongr e).hom.app (dualSheaf N) ≫
        Stacks.Chow.pullbackDualMap g N ≫
          dualMap ((Scheme.Modules.pullbackCongr e).hom.app N) =
      Stacks.Chow.pullbackDualMap f N := by
  subst e
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app]
  exact (Category.id_comp _).trans
    ((congrArg (fun z => Stacks.Chow.pullbackDualMap f N ≫ z)
        (dualMap_id ((Scheme.Modules.pullback f).obj N))).trans (Category.comp_id _))

/-- **The dual base-change map along the structure morphism of a scheme over `Z`**, compared with
the dual base-change maps of the structure morphism of the target and of the morphism itself.
This is `Stacks.Chow.pullbackDualMap_comp` with the structure morphism of the source in place of
the composite, the identification of the two being
`Stacks.FundamentalGroup.pullbackDualMap_congr`. -/
public theorem pullbackDualMap_over {Z : Scheme.{u}} {A B : Over Z} (v : A ⟶ B)
    (N : Z.Modules) :
    (Scheme.Modules.pullbackComp v.left B.hom).hom.app (dualSheaf N) ≫
        ((Scheme.Modules.pullbackCongr (Over.w v)).hom.app (dualSheaf N) ≫
            Stacks.Chow.pullbackDualMap A.hom N ≫
              dualMap ((Scheme.Modules.pullbackCongr (Over.w v)).hom.app N)) ≫
          dualMap ((Scheme.Modules.pullbackComp v.left B.hom).hom.app N) =
      (Scheme.Modules.pullback v.left).map (Stacks.Chow.pullbackDualMap B.hom N) ≫
        Stacks.Chow.pullbackDualMap v.left ((Scheme.Modules.pullback B.hom).obj N) :=
  (congrArg (fun z =>
      (Scheme.Modules.pullbackComp v.left B.hom).hom.app (dualSheaf N) ≫ z ≫
        dualMap ((Scheme.Modules.pullbackComp v.left B.hom).hom.app N))
    (pullbackDualMap_congr (Over.w v) N)).trans
    (Stacks.Chow.pullbackDualMap_comp v.left B.hom N)

/-- **`Stacks.FundamentalGroup.pullbackDualMap_over`, evaluated.** The functional that the dual
base-change map of the structure morphism of `A` attaches to the image of a local section of
`v.left^*(B.hom^*(N^∨))` takes, on the image of a local section of `v.left^*(B.hom^* N)`, the
value that the two dual base-change maps of the factors give. The two sections are arbitrary:
the dual base-change map is characterised against evaluation for every local section. -/
public theorem pullbackDualMap_over_eval {Z : Scheme.{u}} {A B : Over Z} (v : A ⟶ B)
    (N : Z.Modules) (V : A.left.Opens)
    (a : ((Scheme.Modules.pullback v.left).obj
      ((Scheme.Modules.pullback B.hom).obj (dualSheaf N))).val.obj (op V))
    (b : ((Scheme.Modules.pullback v.left).obj
      ((Scheme.Modules.pullback B.hom).obj N)).val.obj (op V)) :
    (((Stacks.Chow.pullbackDualMap A.hom N).val.app (op V)
            (((Scheme.Modules.pullbackCongr (Over.w v)).hom.app (dualSheaf N)).val.app (op V)
              (((Scheme.Modules.pullbackComp v.left B.hom).hom.app (dualSheaf N)).val.app
                (op V) a))).app (op (Over.mk (𝟙 V)))).hom
        (((Scheme.Modules.pullbackCongr (Over.w v)).hom.app N).val.app (op V)
          (((Scheme.Modules.pullbackComp v.left B.hom).hom.app N).val.app (op V) b)) =
      (((Stacks.Chow.pullbackDualMap v.left
            ((Scheme.Modules.pullback B.hom).obj N)).val.app (op V)
          (((Scheme.Modules.pullback v.left).map
            (Stacks.Chow.pullbackDualMap B.hom N)).val.app (op V) a)).app
        (op (Over.mk (𝟙 V)))).hom b :=
  congrArg (fun ψ : (Scheme.Modules.pullback v.left).obj
        ((Scheme.Modules.pullback B.hom).obj (dualSheaf N)) ⟶
      dualSheaf ((Scheme.Modules.pullback v.left).obj
        ((Scheme.Modules.pullback B.hom).obj N)) =>
    dualPairing _ (ψ.val.app (op V) a) (Over.mk (𝟙 V)) b) (pullbackDualMap_over v N)

/-! ### Sections of the dual over a pullback -/

/-- Global sections transported along an isomorphism of modules. -/
public noncomputable def appTopEquiv {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G) :
    Γ(F, (⊤ : X.Opens)) ≃ Γ(G, (⊤ : X.Opens)) where
  toFun x := e.hom.app ⊤ x
  invFun y := e.inv.app ⊤ y
  left_inv x := congrArg (fun χ : F ⟶ F => Scheme.Modules.Hom.app χ ⊤ x) e.hom_inv_id
  right_inv y := congrArg (fun χ : G ⟶ G => Scheme.Modules.Hom.app χ ⊤ y) e.inv_hom_id

/-- The adjoint of a morphism `g^* N ⟶ M` acts on a local section of `N` by sending it to its
canonical image in the pullback and then applying the morphism. -/
private theorem homEquiv_val_app {X Y : Scheme.{u}} (g : Y ⟶ X) (N : X.Modules)
    (M : Y.Modules) (ψ : (Scheme.Modules.pullback g).obj N ⟶ M) (U : X.Opens)
    (m : N.val.obj (op U)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv N M ψ).val.app (op U) m =
      ψ.val.app (op (g ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).val.app (op U) m) :=
  (congrArg (fun χ : N ⟶ (Scheme.Modules.pushforward g).obj M => χ.val.app (op U) m)
      (Adjunction.homEquiv_unit (Scheme.Modules.pullbackPushforwardAdjunction g) N M ψ)).trans
    ((Stacks.Chow.comp_val_app _ _ U m).trans
      (Stacks.Chow.pushforward_map_val_app g ψ U _))

/-- **The sections of `N^∨` over `Y` are the morphisms `N ⟶ g_* 𝒪_Y`.** For a finite locally free
`N` the dual base-change map is invertible, so a section of `g^*(N^∨)` is a section of
`(g^* N)^∨`, which by the degenerate case of [Stacks, Tag 0882] is a morphism `g^* N ⟶ 𝒪_Y`, and
these are the morphisms `N ⟶ g_* 𝒪_Y` by the pullback–pushforward adjunction. -/
public noncomputable def dualNeighborhoodEquiv {X Y : Scheme.{u}} (g : Y ⟶ X) (N : X.Modules)
    (hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N) :
    Γ((Scheme.Modules.pullback g).obj (dualSheaf N), (⊤ : Y.Opens)) ≃
      (N ⟶ (Scheme.Modules.pushforward g).obj (SheafOfModules.unit Y.ringCatSheaf)) :=
  (appTopEquiv (pullbackDualSheafIso g N hN)).trans
    ((dualSectionsHom ((Scheme.Modules.pullback g).obj N)).symm.trans
      ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv N
        (SheafOfModules.unit Y.ringCatSheaf)))

/-- `dualNeighborhoodEquiv` unfolded to the three identifications it composes. -/
public theorem dualNeighborhoodEquiv_apply {X Y : Scheme.{u}} (g : Y ⟶ X) (N : X.Modules)
    (hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N)
    (s : Γ((Scheme.Modules.pullback g).obj (dualSheaf N), (⊤ : Y.Opens))) :
    dualNeighborhoodEquiv g N hN s =
      (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv N
          (SheafOfModules.unit Y.ringCatSheaf)
        ((dualSectionsHom ((Scheme.Modules.pullback g).obj N)).symm
          ((pullbackDualSheafIso g N hN).hom.app ⊤ s)) := rfl

/-- **The component formula for `dualNeighborhoodEquiv`.** The morphism attached to a section `s`
of `g^*(N^∨)` sends a local section `m` of `N` over `U` to the value, on the canonical image of
`m`, of the functional that the dual base-change map attaches to `s` over `g⁻¹U`. -/
public theorem dualNeighborhoodEquiv_val_app {X Y : Scheme.{u}} (g : Y ⟶ X) (N : X.Modules)
    (hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N)
    (s : Γ((Scheme.Modules.pullback g).obj (dualSheaf N), (⊤ : Y.Opens)))
    (U : X.Opens) (m : N.val.obj (op U)) :
    (dualNeighborhoodEquiv g N hN s).val.app (op U) m =
      (((pullbackDualSheafIso g N hN).hom.app ⊤ s).app
          (op (Over.mk (homOfLE (le_top : g ⁻¹ᵁ U ≤ (⊤ : Y.Opens)))))).hom
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).val.app (op U) m) :=
  have h : ((dualSectionsHom ((Scheme.Modules.pullback g).obj N)).symm
        ((pullbackDualSheafIso g N hN).hom.app ⊤ s)).val.app (op (g ⁻¹ᵁ U)) =
      ((pullbackDualSheafIso g N hN).hom.app ⊤ s).app
        (op (Over.mk (homOfLE (le_top : g ⁻¹ᵁ U ≤ (⊤ : Y.Opens))))) :=
    dualSectionsHom_symm_app _ _ (Over.mk (homOfLE le_top))
  (homEquiv_val_app g N _ _ U m).trans (CategoryTheory.congr_fun h _)

/-- **The component formula for `dualNeighborhoodEquiv`, with the section restricted first.**
This is `Stacks.FundamentalGroup.dualNeighborhoodEquiv_val_app` with the dual base-change map
applied to the restriction of `s` to `g⁻¹U` rather than to `s` itself: the functional attached to
a section of `g^*(N^∨)` is determined, at the terminal object of the slice site over `g⁻¹U`, by
that restriction. -/
private theorem dualNeighborhoodEquiv_val_app' {X Y : Scheme.{u}} (g : Y ⟶ X) (N : X.Modules)
    (hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N)
    (s : Γ((Scheme.Modules.pullback g).obj (dualSheaf N), (⊤ : Y.Opens))) (U : X.Opens)
    (m : N.val.obj (op U)) :
    (dualNeighborhoodEquiv g N hN s).val.app (op U) m =
      dualPairing ((Scheme.Modules.pullback g).obj N)
        ((Stacks.Chow.pullbackDualMap g N).val.app (op (g ⁻¹ᵁ U))
          (((Scheme.Modules.pullback g).obj (dualSheaf N)).presheaf.map
            (homOfLE (le_top : g ⁻¹ᵁ U ≤ (⊤ : Y.Opens))).op s))
        (Over.mk (𝟙 (g ⁻¹ᵁ U)))
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).val.app (op U) m) := by
  rw [dualNeighborhoodEquiv_val_app]
  refine Eq.trans ?_ (congrArg (fun z => dualPairing ((Scheme.Modules.pullback g).obj N) z
      (Over.mk (𝟙 (g ⁻¹ᵁ U)))
      (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).val.app (op U) m))
    (PresheafOfModules.naturality_apply (pullbackDualSheafIso g N hN).hom.val
      (homOfLE (le_top : g ⁻¹ᵁ U ≤ (⊤ : Y.Opens))).op s)).symm
  exact (dualPairing_terminal ((Scheme.Modules.pullback g).obj N)
    ((pullbackDualSheafIso g N hN).hom.app ⊤ s)
    (Over.mk (homOfLE (le_top : g ⁻¹ᵁ U ≤ (⊤ : Y.Opens)))) _).symm

/-- Restricting the canonical pullback of a global section to the preimage of an open `U` is the
canonical image of the restriction of that section to `U`. -/
private theorem pullbackGlobalSections_restrict {X Y : Scheme.{u}} (g : Y ⟶ X) (F : X.Modules)
    (t : Γ(F, (⊤ : X.Opens))) (U : X.Opens) :
    ((Scheme.Modules.pullback g).obj F).presheaf.map
        (homOfLE (le_top : g ⁻¹ᵁ U ≤ (⊤ : Y.Opens))).op (pullbackGlobalSections g F t) =
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F).val.app (op U)
        (F.presheaf.map (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op t) := by
  have e : (⊤ : Y.Opens) = g ⁻¹ᵁ (⊤ : X.Opens) := by simp
  have h2 : ((eqToHom e).op ≫ (homOfLE (le_top : g ⁻¹ᵁ U ≤ (⊤ : Y.Opens))).op) =
      ((TopologicalSpace.Opens.map g.base).map
        (homOfLE (le_top : U ≤ (⊤ : X.Opens)))).op :=
    congrArg Quiver.Hom.op (Subsingleton.elim _ _)
  have key : ((Scheme.Modules.pullback g).obj F).presheaf.map (eqToHom e).op ≫
        ((Scheme.Modules.pullback g).obj F).presheaf.map
          (homOfLE (le_top : g ⁻¹ᵁ U ≤ (⊤ : Y.Opens))).op =
      ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj F)).presheaf.map
        (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op := by
    rw [← Functor.map_comp, h2]
    rfl
  exact (CategoryTheory.congr_fun key
      (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F).val.app (op ⊤) t)).trans
    (PresheafOfModules.naturality_apply
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F).val
      (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op t).symm

/-- **The unit square, on components.** The morphism attached to the pullback of the global
section of `N^∨` named by `φ : N ⟶ 𝒪_X` sends a local section `m` of `N` to the pullback of the
function `φ(m)`. -/
public theorem dualNeighborhoodEquiv_pullbackGlobalSections_val_app {X Y : Scheme.{u}}
    (g : Y ⟶ X) (N : X.Modules)
    (hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N)
    (φ : N ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) (U : X.Opens)
    (m : N.val.obj (op U)) :
    (dualNeighborhoodEquiv g N hN
        (pullbackGlobalSections g (dualSheaf N) (dualSectionsHom N φ))).val.app (op U) m =
      (g.app U).hom (φ.val.app (op U) m) := by
  have step2 : (((dualSheaf N).presheaf.map (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op
        (dualSectionsHom N φ)).app (op (Over.mk (𝟙 U)))).hom m = φ.val.app (op U) m :=
    CategoryTheory.congr_fun
      (dualSectionsHom_app N φ (Over.mk (homOfLE (le_top : U ≤ (⊤ : X.Opens))))) m
  rw [dualNeighborhoodEquiv_val_app', pullbackGlobalSections_restrict]
  exact (pullbackDualSheafIso_unit_apply g N hN U _ m).trans
    (congrArg (fun z => (g.app U).hom z) step2)

/-! ### Pullback of a global section along a morphism over the base -/

/-- `AlgebraicGeometry.pullbackSectionsMap` read as the pullback map on global sections along the
underlying morphism, followed by the two canonical comparisons of iterated pullback with pullback
along the composite. -/
private theorem pullbackSectionsMap_apply {S : Scheme.{u}} (F : S.Modules) {A B : Over S}
    (g : A ⟶ B) (s : Γ((Scheme.Modules.pullback B.hom).obj F, (⊤ : B.left.Opens))) :
    pullbackSectionsMap F g s =
      ((Scheme.Modules.pullbackCongr (Over.w g)).hom.app F).app ⊤
        (((Scheme.Modules.pullbackComp g.left B.hom).hom.app F).app ⊤
          (pullbackGlobalSections g.left ((Scheme.Modules.pullback B.hom).obj F) s)) := by
  rw [pullbackGlobalSections_eq_unit]
  exact SectionsEqualizer.presheafMapTop_apply g.left
    ((Scheme.Modules.pullback A.hom).obj F) _

/-- **The pullbacks of a global section form a compatible family.** The canonical map on sections
induced by a morphism of schemes over `S` carries the pullback of a global section of `F` to the
ambient target to its pullback to the source. -/
private theorem pullbackSectionsMap_global {S : Scheme.{u}} (F : S.Modules) {A B : Over S}
    (g : A ⟶ B) (s : Γ(F, (⊤ : S.Opens))) :
    pullbackSectionsMap F g (pullbackGlobalSections B.hom F s) =
      pullbackGlobalSections A.hom F s := by
  rw [pullbackSectionsMap_apply,
    AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp,
    AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_congr]

/-- The comparison of the pullbacks along the two sides of a trivial identification of
morphisms is the identity. -/
private theorem pullbackCongr_hom_app_homMk_rfl {Z Y Y' : Scheme.{u}} (gB : Y ⟶ Z) (w : Y' ⟶ Y)
    (F : Z.Modules) :
    (Scheme.Modules.pullbackCongr (Over.w (Over.homMk w rfl :
        Over.mk (w ≫ gB) ⟶ Over.mk gB))).hom.app F =
      𝟙 ((Scheme.Modules.pullback (w ≫ gB)).obj F) := by
  simp only [Scheme.Modules.pullbackCongr, eqToIso.hom, eqToHom_app]
  exact eqToHom_refl _ _

/-- A morphism of sheaves of modules equal to the identity fixes every local section. -/
private theorem val_app_eq_of_eq_id {X : Scheme.{u}} {M : X.Modules} (f : M ⟶ M) (h : f = 𝟙 M)
    (U : X.Opens) (x : M.val.obj (op U)) : f.val.app (op U) x = x := by
  subst h
  rfl

/-- **The canonical map on sections, restricted to the preimage of an open of the base.** It is
the canonical image of the restriction of the section to the preimage in the target, read through
the two comparisons of iterated pullback with pullback along the composite. -/
private theorem pullbackSectionsMap_restrict {Z Y Y' : Scheme.{u}} (gB : Y ⟶ Z) (w : Y' ⟶ Y)
    (F : Z.Modules) (t : Γ((Scheme.Modules.pullback gB).obj F, (⊤ : Y.Opens))) (U : Z.Opens) :
    ((Scheme.Modules.pullback (w ≫ gB)).obj F).presheaf.map
        (homOfLE (le_top : (w ≫ gB) ⁻¹ᵁ U ≤ (⊤ : Y'.Opens))).op
        (pullbackSectionsMap F (Over.homMk w rfl : Over.mk (w ≫ gB) ⟶ Over.mk gB) t) =
      ((Scheme.Modules.pullbackCongr (Over.w (Over.homMk w rfl :
              Over.mk (w ≫ gB) ⟶ Over.mk gB))).hom.app F).val.app (op ((w ≫ gB) ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackComp w gB).hom.app F).val.app (op ((w ≫ gB) ⁻¹ᵁ U))
          (((Scheme.Modules.pullbackPushforwardAdjunction w).unit.app
              ((Scheme.Modules.pullback gB).obj F)).val.app (op (gB ⁻¹ᵁ U))
            (((Scheme.Modules.pullback gB).obj F).presheaf.map
              (homOfLE (le_top : gB ⁻¹ᵁ U ≤ (⊤ : Y.Opens))).op t))) := by
  refine Eq.trans (congrArg (fun z => ((Scheme.Modules.pullback (w ≫ gB)).obj F).presheaf.map
      (homOfLE (le_top : (w ≫ gB) ⁻¹ᵁ U ≤ (⊤ : Y'.Opens))).op z)
    (pullbackSectionsMap_apply F (Over.homMk w rfl : Over.mk (w ≫ gB) ⟶ Over.mk gB) t)) ?_
  refine (PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullbackCongr (Over.w (Over.homMk w rfl :
      Over.mk (w ≫ gB) ⟶ Over.mk gB))).hom.app F).val
    (homOfLE (le_top : (w ≫ gB) ⁻¹ᵁ U ≤ (⊤ : Y'.Opens))).op _).symm.trans ?_
  refine congrArg (fun z => ((Scheme.Modules.pullbackCongr (Over.w (Over.homMk w rfl :
        Over.mk (w ≫ gB) ⟶ Over.mk gB))).hom.app F).val.app (op ((w ≫ gB) ⁻¹ᵁ U)) z) ?_
  refine (PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullbackComp w gB).hom.app F).val
    (homOfLE (le_top : (w ≫ gB) ⁻¹ᵁ U ≤ (⊤ : Y'.Opens))).op _).symm.trans ?_
  exact congrArg (fun z => ((Scheme.Modules.pullbackComp w gB).hom.app F).val.app
      (op ((w ≫ gB) ⁻¹ᵁ U)) z)
    (pullbackGlobalSections_restrict w ((Scheme.Modules.pullback gB).obj F) t (gB ⁻¹ᵁ U))

/-! ### The transition square -/

/-- **The transition square.** Let `w : Y' ⟶ Y` be a morphism of schemes over `Z`, so that the
structure morphism of the source is `w ≫ gB`. Under the identification of the sections of `N^∨`
over a scheme over `Z` with the morphisms `N ⟶` (direct image of the structure sheaf), the
canonical map on sections induced by `w` corresponds to composition with the canonical map of
direct image algebras.

Both sides are morphisms out of `N`, and the proof takes their components on `N`: a morphism
`N ⟶ g_* 𝒪` is determined by its values on the canonical images of local sections of `N`, and on
exactly those images the dual base-change map of `w` is computed by
`Stacks.Chow.pullbackDualMap_eval` together with `Stacks.Chow.pullbackEvaluation_unit_tmul`. The
section fed to the dual base-change map of `w ≫ gB` is *not* a canonical image, and that is what
`Stacks.FundamentalGroup.pullbackDualMap_over_eval` — hence
`Stacks.Chow.pullbackDualMap_comp` — is for. -/
public theorem dualNeighborhoodEquiv_pullbackSectionsMap {Z Y Y' : Scheme.{u}}
    {gA : Y' ⟶ Z} (gB : Y ⟶ Z) (w : Y' ⟶ Y) (e : w ≫ gB = gA) (N : Z.Modules)
    (hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N)
    (t : Γ((Scheme.Modules.pullback gB).obj (dualSheaf N), (⊤ : Y.Opens))) :
    dualNeighborhoodEquiv gA N hN
        (pullbackSectionsMap (dualSheaf N)
          (Over.homMk w e : Over.mk gA ⟶ Over.mk gB) t) =
      dualNeighborhoodEquiv gB N hN t ≫
        AlgebraSheaf.underlyingModuleMap
          (Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap
            (Over.homMk w e : Over.mk gA ⟶ Over.mk gB)) := by
  subst e
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
  obtain ⟨U⟩ := U
  have hle := Stacks.AffineAlgebraEquivalence.preimage_le_preimage_preimage
    (Over.homMk w rfl : Over.mk (w ≫ gB) ⟶ Over.mk gB) U
  -- the canonical image of `m` in the iterated pullback is the canonical image in the pullback
  -- along the composite
  have hb : ((Scheme.Modules.pullbackCongr (Over.w (Over.homMk w rfl :
          Over.mk (w ≫ gB) ⟶ Over.mk gB))).hom.app N).val.app (op ((w ≫ gB) ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackComp w gB).hom.app N).val.app (op ((w ≫ gB) ⁻¹ᵁ U))
          (((Scheme.Modules.pullbackPushforwardAdjunction w).unit.app
              ((Scheme.Modules.pullback gB).obj N)).val.app (op (gB ⁻¹ᵁ U))
            (((Scheme.Modules.pullbackPushforwardAdjunction gB).unit.app N).val.app
              (op U) m))) =
      ((Scheme.Modules.pullbackPushforwardAdjunction (w ≫ gB)).unit.app N).val.app (op U) m := by
    rw [← Scheme.Modules.pullbackComp_inv_unit w gB N U m]
    exact (val_app_eq_of_eq_id _ (pullbackCongr_hom_app_homMk_rfl gB w N) _ _).trans
      (val_app_eq_of_eq_id _ ((Scheme.Modules.pullbackComp w gB).app N).inv_hom_id _ _)
  -- the right-hand side: the component of the algebra map is the comorphism of `w`
  have hR : (dualNeighborhoodEquiv gB N hN t ≫
        AlgebraSheaf.underlyingModuleMap
          (Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap (Over.homMk w rfl :
            Over.mk (w ≫ gB) ⟶ Over.mk gB))).val.app (op U) m =
      (w.app (gB ⁻¹ᵁ U)).hom
        (dualPairing ((Scheme.Modules.pullback gB).obj N)
          ((Stacks.Chow.pullbackDualMap gB N).val.app (op (gB ⁻¹ᵁ U))
            (((Scheme.Modules.pullback gB).obj (dualSheaf N)).presheaf.map
              (homOfLE (le_top : gB ⁻¹ᵁ U ≤ (⊤ : Y.Opens))).op t))
          (Over.mk (𝟙 (gB ⁻¹ᵁ U)))
          (((Scheme.Modules.pullbackPushforwardAdjunction gB).unit.app N).val.app
            (op U) m)) := by
    refine (Stacks.Chow.comp_val_app _ _ U m).trans ?_
    refine Eq.trans ?_ (congrArg (fun z => (w.app (gB ⁻¹ᵁ U)).hom z)
      (dualNeighborhoodEquiv_val_app' gB N hN t U m))
    refine (congrArg (fun ψ => ψ.hom
        ((dualNeighborhoodEquiv gB N hN t).val.app (op U) m))
      (Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap_app (Over.homMk w rfl :
        Over.mk (w ≫ gB) ⟶ Over.mk gB) U hle)).trans ?_
    exact congrArg (fun ψ => ψ.hom
        ((dualNeighborhoodEquiv gB N hN t).val.app (op U) m))
      (w.appLE_eq_app : w.appLE (gB ⁻¹ᵁ U) ((w ≫ gB) ⁻¹ᵁ U) hle = w.app (gB ⁻¹ᵁ U))
  refine Eq.trans ?_ hR.symm
  -- the left-hand side
  refine (dualNeighborhoodEquiv_val_app' (w ≫ gB) N hN _ U m).trans ?_
  refine Eq.trans (congrArg (fun z =>
      dualPairing ((Scheme.Modules.pullback (w ≫ gB)).obj N)
        ((Stacks.Chow.pullbackDualMap (w ≫ gB) N).val.app (op ((w ≫ gB) ⁻¹ᵁ U)) z)
        (Over.mk (𝟙 ((w ≫ gB) ⁻¹ᵁ U)))
        (((Scheme.Modules.pullbackPushforwardAdjunction (w ≫ gB)).unit.app N).val.app
          (op U) m))
    (pullbackSectionsMap_restrict gB w (dualSheaf N) t U)) ?_
  refine Eq.trans (congrArg (fun z =>
      dualPairing ((Scheme.Modules.pullback (w ≫ gB)).obj N)
        ((Stacks.Chow.pullbackDualMap (w ≫ gB) N).val.app (op ((w ≫ gB) ⁻¹ᵁ U))
          (((Scheme.Modules.pullbackCongr (Over.w (Over.homMk w rfl :
                Over.mk (w ≫ gB) ⟶ Over.mk gB))).hom.app (dualSheaf N)).val.app
              (op ((w ≫ gB) ⁻¹ᵁ U))
            (((Scheme.Modules.pullbackComp w gB).hom.app (dualSheaf N)).val.app
              (op ((w ≫ gB) ⁻¹ᵁ U))
              (((Scheme.Modules.pullbackPushforwardAdjunction w).unit.app
                  ((Scheme.Modules.pullback gB).obj (dualSheaf N))).val.app (op (gB ⁻¹ᵁ U))
                (((Scheme.Modules.pullback gB).obj (dualSheaf N)).presheaf.map
                  (homOfLE (le_top : gB ⁻¹ᵁ U ≤ (⊤ : Y.Opens))).op t)))))
        (Over.mk (𝟙 ((w ≫ gB) ⁻¹ᵁ U))) z)
    hb.symm) ?_
  refine (pullbackDualMap_over_eval (Over.homMk w rfl : Over.mk (w ≫ gB) ⟶ Over.mk gB) N
    ((w ≫ gB) ⁻¹ᵁ U) _ _).trans ?_
  refine Eq.trans (congrArg (fun z =>
      (((Stacks.Chow.pullbackDualMap w ((Scheme.Modules.pullback gB).obj N)).val.app
          (op ((w ≫ gB) ⁻¹ᵁ U)) z).app (op (Over.mk (𝟙 ((w ≫ gB) ⁻¹ᵁ U))))).hom
        (((Scheme.Modules.pullbackPushforwardAdjunction w).unit.app
            ((Scheme.Modules.pullback gB).obj N)).val.app (op (gB ⁻¹ᵁ U))
          (((Scheme.Modules.pullbackPushforwardAdjunction gB).unit.app N).val.app (op U) m)))
    (Stacks.Chow.pullback_map_unit_app w (Stacks.Chow.pullbackDualMap gB N) (gB ⁻¹ᵁ U)
      (((Scheme.Modules.pullback gB).obj (dualSheaf N)).presheaf.map
        (homOfLE (le_top : gB ⁻¹ᵁ U ≤ (⊤ : Y.Opens))).op t))) ?_
  exact (Stacks.Chow.pullbackDualMap_eval w ((Scheme.Modules.pullback gB).obj N)
      ((w ≫ gB) ⁻¹ᵁ U) _ _).trans
    (Stacks.Chow.pullbackEvaluation_unit_tmul w ((Scheme.Modules.pullback gB).obj N)
      (gB ⁻¹ᵁ U) _ _)

/-! ### The direct image algebras of two neighbourhoods -/

variable {Z Z' : Scheme.{u}} (κ : Z' ⟶ Z) [IsClosedImmersion κ]

/-- **A morphism of schemes over `Z` into `Z` itself is unique.** Its underlying morphism is
forced to be the structure morphism of the source. -/
public theorem over_id_hom_ext {W : Over Z} (a b : W ⟶ Over.mk (𝟙 Z)) : a = b :=
  Over.OverMorphism.ext
    (((Category.comp_id a.left).symm.trans (Over.w a)).trans
      ((Category.comp_id b.left).symm.trans (Over.w b)).symm)

/-- The inclusions of the infinitesimal neighbourhoods compose. -/
public theorem nthInfinitesimalNeighbourhoodTransition_comp {n m k : ℕ} (h₁ : n ≤ m)
    (h₂ : m ≤ k) :
    nthInfinitesimalNeighbourhoodTransition κ h₁ ≫ nthInfinitesimalNeighbourhoodTransition κ h₂ =
      nthInfinitesimalNeighbourhoodTransition κ (h₁.trans h₂) :=
  Over.OverMorphism.ext (Scheme.IdealSheafData.inclusion_comp _ _)

/-- The inclusion of an infinitesimal neighbourhood into itself is the identity. -/
public theorem nthInfinitesimalNeighbourhoodTransition_refl (n : ℕ) :
    nthInfinitesimalNeighbourhoodTransition κ (le_refl n) =
      𝟙 (nthInfinitesimalNeighbourhoodOver κ n) :=
  Over.OverMorphism.ext (Scheme.IdealSheafData.inclusion_id _)

/-- Taking underlying modules is compatible with composition of morphisms of algebra sheaves. -/
public theorem underlyingModuleMap_id' {X : Scheme.{u}} (A : AlgebraSheaf X) :
    AlgebraSheaf.underlyingModuleMap (𝟙 A) = 𝟙 (AlgebraSheaf.underlyingModule A) :=
  (AlgebraSheaf.underlyingModuleFunctor X).map_id A

/-- Taking underlying modules is compatible with composition of morphisms of algebra sheaves. -/
public theorem underlyingModuleMap_comp' {X : Scheme.{u}} {A B C : AlgebraSheaf X}
    (f : A ⟶ B) (g : B ⟶ C) :
    AlgebraSheaf.underlyingModuleMap f ≫ AlgebraSheaf.underlyingModuleMap g =
      AlgebraSheaf.underlyingModuleMap (f ≫ g) :=
  ((AlgebraSheaf.underlyingModuleFunctor X).map_comp f g).symm

/-- The map of direct image algebras `(ι_m) _* 𝒪_{Z'_m} ⟶ (ι_n) _* 𝒪_{Z'_n}` induced by the
inclusion of the `n`-th infinitesimal neighbourhood into the `m`-th, for `n ≤ m`. -/
public def nthOrderTransitionMapLE {n m : ℕ} (h : n ≤ m) :
    AlgebraSheaf.underlyingModule (nthOrderAlgebra κ m) ⟶
      AlgebraSheaf.underlyingModule (nthOrderAlgebra κ n) :=
  AlgebraSheaf.underlyingModuleMap
    (Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap
      (nthInfinitesimalNeighbourhoodTransition κ h))

/-- The successor case of `nthOrderTransitionMapLE` is `nthOrderTransitionMap`. -/
public theorem nthOrderTransitionMapLE_succ (n : ℕ) :
    nthOrderTransitionMapLE κ (Nat.le_succ n) = nthOrderTransitionMap κ n := by
  unfold nthOrderTransitionMapLE nthOrderTransitionMap nthOrderAlgebraTransition
  exact congrArg
    (fun hh : n ≤ n + 1 => AlgebraSheaf.underlyingModuleMap
      (Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap
        (nthInfinitesimalNeighbourhoodTransition κ hh)))
    (proof_irrel _ _)

/-- The canonical map `𝒪_Z ⟶ (ι_n) _* 𝒪_{Z'_n}` acts on local functions as the comorphism of the
structure morphism of the `n`-th infinitesimal neighbourhood. -/
public theorem nthOrderUnitMap_val_app (n : ℕ) (U : Z.Opens)
    (r : (SheafOfModules.unit Z.ringCatSheaf).val.obj (op U)) :
    (nthOrderUnitMap κ n).val.app (op U) r =
      ((nthOrderToBase κ n).appLE (𝟙 Z ⁻¹ᵁ U)
        (nthInfinitesimalNeighbourhoodι κ n ⁻¹ᵁ U) le_rfl).hom r :=
  congrArg (fun ψ => ψ.hom r)
    (Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMapAux_app (𝟙 Z)
      (nthOrderToBase κ n) (nthInfinitesimalNeighbourhoodι κ n)
      (Category.comp_id (nthOrderToBase κ n)) U le_rfl)

/-- The canonical map `𝒪_Z ⟶ (ι_n) _* 𝒪_{Z'_n}` acts on local functions by the comorphism of
`ι_n`. This is `Stacks.FundamentalGroup.nthOrderUnitMap_val_app` with the restriction map of the
preimage of `U` under the identity removed. -/
public theorem nthOrderUnitMap_val_app' (n : ℕ) (U : Z.Opens)
    (r : (SheafOfModules.unit Z.ringCatSheaf).val.obj (op U)) :
    (nthOrderUnitMap κ n).val.app (op U) r =
      ((nthInfinitesimalNeighbourhoodι κ n).app U).hom r := by
  have h : (nthOrderToBase κ n).appLE (𝟙 Z ⁻¹ᵁ U)
      (nthInfinitesimalNeighbourhoodι κ n ⁻¹ᵁ U) le_rfl =
      (nthInfinitesimalNeighbourhoodι κ n).app U := (nthOrderToBase κ n).appLE_eq_app
  rw [nthOrderUnitMap_val_app, h]
  rfl

/-- **The canonical map `𝒪_Z ⟶ (ι_n) _* 𝒪_{Z'_n}` is the adjoint of the structure-sheaf
comparison `ι_n^* 𝒪_Z ⟶ 𝒪_{Z'_n}`**: it is the unit of the pullback–pushforward adjunction at
the structure sheaf, followed by the direct image of that comparison. -/
public theorem nthOrderUnitMap_eq_unit (n : ℕ) :
    nthOrderUnitMap κ n =
      (Scheme.Modules.pullbackPushforwardAdjunction
          (nthInfinitesimalNeighbourhoodι κ n)).unit.app
            (SheafOfModules.unit Z.ringCatSheaf) ≫
        (Scheme.Modules.pushforward (nthInfinitesimalNeighbourhoodι κ n)).map
          (SheafOfModules.pullbackObjUnitToUnit
            (RingedSpaceModuleAdjunction.structureSheafHom
              (nthInfinitesimalNeighbourhoodι κ n).toLRSHom.toShHom)) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun r => ?_)
  rw [nthOrderUnitMap_val_app' κ n U.unop r]
  refine Eq.trans ?_ (Stacks.Chow.comp_val_app _ _ U.unop r).symm
  exact (Stacks.Chow.pullbackObjUnitToUnit_unit_app
    (nthInfinitesimalNeighbourhoodι κ n) U.unop r).symm

/-- **The unit square.** Restricting a global section of `N^∨` to the `n`-th infinitesimal
neighbourhood corresponds, under the identification of the sections of `N^∨` there with the
morphisms `N ⟶ (ι_n) _* 𝒪_{Z'_n}`, to composing the morphism `N ⟶ 𝒪_Z` that the section names
with the canonical map `𝒪_Z ⟶ (ι_n) _* 𝒪_{Z'_n}`. -/
public theorem dualSectionsHom_pullbackGlobalSections (n : ℕ) (N : Z.Modules)
    (hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N)
    (φ : N ⟶ (SheafOfModules.unit Z.ringCatSheaf : Z.Modules)) :
    dualNeighborhoodEquiv (nthInfinitesimalNeighbourhoodι κ n) N hN
        (pullbackGlobalSections (nthInfinitesimalNeighbourhoodι κ n) (dualSheaf N)
          (dualSectionsHom N φ)) =
      φ ≫ nthOrderUnitMap κ n := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
  rw [dualNeighborhoodEquiv_pullbackGlobalSections_val_app]
  exact ((Stacks.Chow.comp_val_app φ (nthOrderUnitMap κ n) U.unop m).trans
    (nthOrderUnitMap_val_app' κ n U.unop _)).symm

/-- The maps of direct image algebras compose. -/
public theorem nthOrderTransitionMapLE_comp {n m k : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ k) :
    nthOrderTransitionMapLE κ h₂ ≫ nthOrderTransitionMapLE κ h₁ =
      nthOrderTransitionMapLE κ (h₁.trans h₂) := by
  rw [nthOrderTransitionMapLE, nthOrderTransitionMapLE, nthOrderTransitionMapLE,
    underlyingModuleMap_comp', ← nthInfinitesimalNeighbourhoodTransition_comp κ h₁ h₂,
    Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap_comp]

/-- The map of direct image algebras of a neighbourhood with itself is the identity. -/
public theorem nthOrderTransitionMapLE_refl (n : ℕ) :
    nthOrderTransitionMapLE κ (le_refl n) =
      𝟙 (AlgebraSheaf.underlyingModule (nthOrderAlgebra κ n)) := by
  rw [nthOrderTransitionMapLE, nthInfinitesimalNeighbourhoodTransition_refl,
    Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap_id]
  exact underlyingModuleMap_id' _

/-- **The canonical maps `𝒪_Z ⟶ (ι_n) _* 𝒪_{Z'_n}` are compatible with the maps of direct image
algebras.** Both are induced by morphisms of schemes over `Z` into `Z` itself, and such a
morphism is unique. -/
public theorem nthOrderUnitMap_comp_nthOrderTransitionMapLE {n m : ℕ} (h : n ≤ m) :
    nthOrderUnitMap κ m ≫ nthOrderTransitionMapLE κ h = nthOrderUnitMap κ n := by
  have h1 : nthInfinitesimalNeighbourhoodTransition κ h ≫
      (Over.homMk (nthOrderToBase κ m) (Category.comp_id (nthOrderToBase κ m)) :
        nthInfinitesimalNeighbourhoodOver κ m ⟶ Over.mk (𝟙 Z)) =
      (Over.homMk (nthOrderToBase κ n) (Category.comp_id (nthOrderToBase κ n)) :
        nthInfinitesimalNeighbourhoodOver κ n ⟶ Over.mk (𝟙 Z)) :=
    over_id_hom_ext _ _
  have hAB : nthOrderAlgebraRestriction κ m ≫
        Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap
          (nthInfinitesimalNeighbourhoodTransition κ h) =
      nthOrderAlgebraRestriction κ n := by
    rw [nthOrderAlgebraRestriction, nthOrderAlgebraRestriction,
      ← Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap_comp, h1]
  exact (underlyingModuleMap_comp' (nthOrderAlgebraRestriction κ m)
      (Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap
        (nthInfinitesimalNeighbourhoodTransition κ h))).trans
    (congrArg AlgebraSheaf.underlyingModuleMap hAB)

/-- **A family of morphisms compatible with the successive transition maps is compatible with all
of them.** This is the passage from the successor-indexed compatibility that
`Stacks.FundamentalGroup.DualSectionsHypothesis` states to the `n ≤ m` indexed compatibility that
`Stacks.Algebraization.IsInfinitesimalSectionsComplete` uses. -/
public theorem transitionMapLE_compatible (N : Z.Modules)
    (α : ∀ n : ℕ, N ⟶ AlgebraSheaf.underlyingModule (nthOrderAlgebra κ n))
    (hα : ∀ n : ℕ, α (n + 1) ≫ nthOrderTransitionMap κ n = α n) :
    ∀ (n m : ℕ) (h : n ≤ m), α m ≫ nthOrderTransitionMapLE κ h = α n := by
  intro n m h
  induction m, h using Nat.le_induction with
  | base => rw [nthOrderTransitionMapLE_refl, Category.comp_id]
  | succ m hnm ih =>
      have hcomp := nthOrderTransitionMapLE_comp κ hnm (Nat.le_succ m)
      calc α (m + 1) ≫ nthOrderTransitionMapLE κ (hnm.trans (Nat.le_succ m))
          = α (m + 1) ≫ nthOrderTransitionMapLE κ (Nat.le_succ m) ≫
              nthOrderTransitionMapLE κ hnm := by rw [← hcomp]
        _ = (α (m + 1) ≫ nthOrderTransitionMap κ m) ≫ nthOrderTransitionMapLE κ hnm := by
              rw [← Category.assoc, nthOrderTransitionMapLE_succ]
        _ = α n := by rw [hα m, ih]

/-- **The first clause of `Stacks.FundamentalGroup.DualSectionsHypothesis`:** for a finite locally
free `N` whose dual has its global sections complete along the infinitesimal neighbourhoods, two
morphisms `N ⟶ 𝒪_Z` that agree after composition with every canonical map
`𝒪_Z ⟶ (ι_n) _* 𝒪_{Z'_n}` are equal.

Both morphisms name global sections of `N^∨`, the pullbacks of those two sections to the
neighbourhoods agree by the unit square and the injectivity of
`Stacks.FundamentalGroup.dualNeighborhoodEquiv`, and the pullbacks of a global section are a
compatible family, so the uniqueness half of completeness identifies the two sections. -/
public theorem nthOrderUnitMap_jointly_injective (N : Z.Modules)
    (hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N)
    (hc : Stacks.Algebraization.IsInfinitesimalSectionsComplete κ (dualSheaf N))
    (φ ψ : N ⟶ (SheafOfModules.unit Z.ringCatSheaf : Z.Modules))
    (h : ∀ n : ℕ, φ ≫ nthOrderUnitMap κ n = ψ ≫ nthOrderUnitMap κ n) : φ = ψ := by
  obtain ⟨t, -, htuniq⟩ := hc
    (fun n => pullbackGlobalSections (nthInfinitesimalNeighbourhoodι κ n) (dualSheaf N)
      (dualSectionsHom N φ))
    (fun n m hnm => pullbackSectionsMap_global (dualSheaf N)
      (nthInfinitesimalNeighbourhoodTransition κ hnm) (dualSectionsHom N φ))
  have e2 : dualSectionsHom N ψ = t :=
    htuniq _ fun n =>
      (dualNeighborhoodEquiv (nthInfinitesimalNeighbourhoodι κ n) N hN).injective
        ((dualSectionsHom_pullbackGlobalSections κ n N hN ψ).trans
          ((h n).symm.trans (dualSectionsHom_pullbackGlobalSections κ n N hN φ).symm))
  exact (dualSectionsHom N).injective ((htuniq _ fun n => rfl).trans e2.symm)

/-- **The transition square for the infinitesimal neighbourhoods.** This is
`Stacks.FundamentalGroup.dualNeighborhoodEquiv_pullbackSectionsMap` at the inclusion of the
`n`-th infinitesimal neighbourhood into the `m`-th, where the canonical map of direct image
algebras is `Stacks.FundamentalGroup.nthOrderTransitionMapLE`. -/
public theorem dualNeighborhoodEquiv_pullbackSectionsMap_transition (N : Z.Modules)
    (hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N) {n m : ℕ}
    (h : n ≤ m)
    (t : Γ((Scheme.Modules.pullback (nthInfinitesimalNeighbourhoodι κ m)).obj (dualSheaf N),
      (⊤ : (nthInfinitesimalNeighbourhoodOver κ m).left.Opens))) :
    dualNeighborhoodEquiv (nthInfinitesimalNeighbourhoodι κ n) N hN
        (pullbackSectionsMap (dualSheaf N) (nthInfinitesimalNeighbourhoodTransition κ h) t) =
      dualNeighborhoodEquiv (nthInfinitesimalNeighbourhoodι κ m) N hN t ≫
        nthOrderTransitionMapLE κ h := by
  have hv : (Over.homMk (nthInfinitesimalNeighbourhoodTransition κ h).left
        (Over.w (nthInfinitesimalNeighbourhoodTransition κ h)) :
      nthInfinitesimalNeighbourhoodOver κ n ⟶ nthInfinitesimalNeighbourhoodOver κ m) =
      nthInfinitesimalNeighbourhoodTransition κ h := Over.OverMorphism.ext rfl
  refine Eq.trans (congrArg (fun v : nthInfinitesimalNeighbourhoodOver κ n ⟶
      nthInfinitesimalNeighbourhoodOver κ m =>
    dualNeighborhoodEquiv (nthInfinitesimalNeighbourhoodι κ n) N hN
      (pullbackSectionsMap (dualSheaf N) v t)) hv.symm) ?_
  refine Eq.trans (dualNeighborhoodEquiv_pullbackSectionsMap
    (nthInfinitesimalNeighbourhoodι κ m) (nthInfinitesimalNeighbourhoodTransition κ h).left
    (Over.w (nthInfinitesimalNeighbourhoodTransition κ h)) N hN t) ?_
  exact congrArg (fun v : nthInfinitesimalNeighbourhoodOver κ n ⟶
      nthInfinitesimalNeighbourhoodOver κ m =>
    dualNeighborhoodEquiv (nthInfinitesimalNeighbourhoodι κ m) N hN t ≫
      AlgebraSheaf.underlyingModuleMap
        (Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap v)) hv

/-- **The second clause of `Stacks.FundamentalGroup.DualSectionsHypothesis`:** for a finite
locally free `N` whose dual has its global sections complete along the infinitesimal
neighbourhoods, a family of morphisms `N ⟶ (ι_n) _* 𝒪_{Z'_n}` compatible with the maps of direct
image algebras comes from a morphism `N ⟶ 𝒪_Z`.

Each member of the family names a section of `N^∨` over the corresponding neighbourhood; the
transition square turns the compatibility of the family into the compatibility that completeness
asks for, and the existence half of completeness produces a global section of `N^∨`, which is a
morphism `N ⟶ 𝒪_Z` whose composites with the canonical maps of the tower are the family again by
the unit square. -/
public theorem exists_hom_of_nthOrderUnitMap_compatible (N : Z.Modules)
    (hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N)
    (hc : Stacks.Algebraization.IsInfinitesimalSectionsComplete κ (dualSheaf N))
    (α : ∀ n : ℕ, N ⟶ AlgebraSheaf.underlyingModule (nthOrderAlgebra κ n))
    (hα : ∀ n : ℕ, α (n + 1) ≫ nthOrderTransitionMap κ n = α n) :
    ∃ φ : N ⟶ (SheafOfModules.unit Z.ringCatSheaf : Z.Modules),
      ∀ n : ℕ, φ ≫ nthOrderUnitMap κ n = α n := by
  obtain ⟨T, hT, -⟩ := hc
    (fun n => (dualNeighborhoodEquiv (nthInfinitesimalNeighbourhoodι κ n) N hN).symm (α n))
    (fun n m h => (dualNeighborhoodEquiv (nthInfinitesimalNeighbourhoodι κ n) N hN).injective
      (((dualNeighborhoodEquiv_pullbackSectionsMap_transition κ N hN h _).trans
          ((congrArg (fun z => z ≫ nthOrderTransitionMapLE κ h)
              ((dualNeighborhoodEquiv (nthInfinitesimalNeighbourhoodι κ m) N hN).apply_symm_apply
                (α m))).trans
            (transitionMapLE_compatible κ N α hα n m h))).trans
        ((dualNeighborhoodEquiv (nthInfinitesimalNeighbourhoodι κ n) N hN).apply_symm_apply
          (α n)).symm))
  refine ⟨(dualSectionsHom N).symm T, fun n => ?_⟩
  refine (dualSectionsHom_pullbackGlobalSections κ n N hN
    ((dualSectionsHom N).symm T)).symm.trans ?_
  refine Eq.trans (congrArg (fun z => dualNeighborhoodEquiv
      (nthInfinitesimalNeighbourhoodι κ n) N hN
      (pullbackGlobalSections (nthInfinitesimalNeighbourhoodι κ n) (dualSheaf N) z))
    ((dualSectionsHom N).apply_symm_apply T)) ?_
  refine Eq.trans (congrArg (dualNeighborhoodEquiv (nthInfinitesimalNeighbourhoodι κ n) N hN)
    (hT n)) ?_
  exact (dualNeighborhoodEquiv (nthInfinitesimalNeighbourhoodι κ n) N hN).apply_symm_apply (α n)

end Stacks.FundamentalGroup

end
