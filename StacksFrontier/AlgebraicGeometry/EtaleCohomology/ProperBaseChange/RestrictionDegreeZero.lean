module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SeparablyClosedBaseFieldSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SubmersiveSectionsRestriction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The restriction map in degree zero

For a morphism of schemes `i : Y ⟶ X` and an abelian sheaf `F` on the small étale site of `X`,
the restriction map `H^0(X, F) → H^0(Y, i^{-1} F)` of
`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap` is bijective exactly when the unit
`F ⟶ i_* i^{-1} F` of the inverse-image adjunction is bijective on sections over the final
object of `X_étale`, and that is the same for the underlying sheaf of sets of `F`. When `i` is
universally submersive with geometrically connected fibres the latter holds by Stacks Project
Tag 0EZK, `Stacks.EtaleCohomology.isIso_globalSectionsSmallEtaleInverseImage`.

In particular, for a scheme `X` over a separably closed field `k` and an arbitrary field
extension `k'/k`, restriction to `X_{k'}` is bijective in degree zero for every abelian sheaf.
This is the degree-zero case of statements (6) and (7) of Stacks Project Situation 0A52, and it
needs neither properness nor a dimension bound.

## Main results

* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_zero_bijective_iff_unit` — degree-zero
  restriction is the unit on final sections.
* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_zero_bijective_of_isIso` — bijectivity
  in degree zero when the comparison of global sections of sheaves of sets is invertible.
* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_zero_bijective_of_isSepClosed` — the
  scalar-extension case.

## Implementation notes

The underlying sheaf of sets of an inverse image of abelian sheaves is the inverse image of the
underlying sheaf of sets by `Stacks.EtaleCohomology.coefficientPullbackComparison_unit`, the
forgetful functor preserving the relevant left Kan extensions
(`Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange`). The
coefficients are `AddCommGrpCat.{u + 1}`, the universe at which that statement is available.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u w

namespace Stacks.EtaleCohomology

section Abelian

variable {X Y : Scheme.{u}} (i : Y ⟶ X)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- If `f ∘ a = b ∘ g` with `a` and `b` bijective, then `f` is bijective exactly when `g` is. -/
private theorem bijective_iff_of_comp_eq {α β γ δ : Type*} {f : α → β} {g : γ → δ} {a : γ → α}
    {b : δ → β} (ha : Function.Bijective a) (hb : Function.Bijective b) (h : f ∘ a = b ∘ g) :
    Function.Bijective f ↔ Function.Bijective g := by
  rw [← Function.Bijective.of_comp_iff _ ha, h, Function.Bijective.of_comp_iff' hb]

/-- Postcomposition with a morphism `u : H ⟶ H'` of abelian groups on morphisms out of `ℤ` is
bijective exactly when `u` is. -/
lemma bijective_postcomp_uliftZ_iff {H H' : AddCommGrpCat.{u + 1}} (g : H ⟶ H') :
    Function.Bijective (fun φ : AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶ H ↦ φ ≫ g) ↔
      Function.Bijective g := by
  let e := AddCommGrpCat.coyonedaObjIsoForget.{u + 1}
  exact (bijective_iff_of_comp_eq (f := fun x ↦ g x) (a := e.hom.app H) (b := e.hom.app H')
    ((isIso_iff_bijective _).mp inferInstance) ((isIso_iff_bijective _).mp inferInstance)
    (funext fun φ ↦ ConcreteCategory.congr_hom (e.hom.naturality g) φ).symm).symm

/-- **Restriction in degree zero is the unit on final sections.** For any terminal object `T`
of the small étale site of `X`, the restriction map `H^0(X, F) → H^0(Y, i^{-1} F)` is bijective
exactly when the unit `F ⟶ i_* i^{-1} F` is bijective on sections over `T`. -/
theorem etaleCohomologyRestrictionMap_zero_bijective_iff_unit {T : X.Etale} (hT : IsTerminal T)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, w} i F 0) ↔
      Function.Bijective
        (((etaleAbelianInverseImageDirectImageAdj.{u, 0} i).unit.app F).hom.app (op T)) := by
  let G := etaleAbelianInverseImage.{u, 0} i
  let adj := etaleAbelianInverseImageDirectImageAdj.{u, 0} i
  let Z := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  rw [etaleCohomologyRestrictionMap_bijective_iff]
  let c := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} hT
  -- step 1: through `Ext.mk₀`
  refine (bijective_iff_of_comp_eq (Ext.mk₀_bijective Z F) (Ext.mk₀_bijective _ _)
    (funext fun φ ↦ Ext.mapExactFunctor_mk₀ G φ)).trans ?_
  -- step 2: through the adjunction
  refine (bijective_iff_of_comp_eq (a := id) (b := adj.homEquiv Z (G.obj F)) Function.bijective_id
    (adj.homEquiv Z (G.obj F)).bijective (g := G.map) (f := fun φ ↦ φ ≫ adj.unit.app F)
    (funext fun φ ↦ by
      rw [Function.comp_apply, Function.comp_apply, Adjunction.homEquiv_unit]
      exact adj.unit.naturality φ)).symm.trans ?_
  -- step 3: through the constant-sheaf adjunction at `T`
  refine (bijective_iff_of_comp_eq (c.homEquiv _ _).bijective (c.homEquiv _ _).bijective
    (g := fun φ : Z ⟶ F ↦ φ ≫ adj.unit.app F)
    (f := fun ψ ↦ ψ ≫ ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op T)).map (adj.unit.app F))
    (funext fun φ ↦ c.homEquiv_naturality_right φ (adj.unit.app F)).symm).symm.trans ?_
  exact bijective_postcomp_uliftZ_iff _

omit [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})] in
/-- **Degree-zero restriction via sheaves of sets.** The unit of the abelian inverse-image
adjunction is bijective on sections over `T` exactly when the unit of the inverse-image
adjunction of sheaves of sets is, at the underlying sheaf of sets. -/
theorem bijective_etaleAbelianUnit_app_iff_set {T : X.Etale}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Function.Bijective
        (((etaleAbelianInverseImageDirectImageAdj.{u, 0} i).unit.app F).hom.app (op T)) ↔
      Function.Bijective (((smallEtaleInverseImageAdjunction.{u, 0} i).unit.app
        ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj F)).hom.app
          (op T)) := by
  have hiso : IsIso (coefficientPullbackComparison (smallEtaleBaseChange i) X.smallEtaleTopology
      Y.smallEtaleTopology (forget AddCommGrpCat.{u + 1}) F) := by
    rw [← coefficientPullbackTwoSquare_app]
    infer_instance
  exact bijective_iff_of_comp_eq (a := id) Function.bijective_id
    (b := (coefficientPullbackComparison (smallEtaleBaseChange i) X.smallEtaleTopology
      Y.smallEtaleTopology (forget AddCommGrpCat.{u + 1}) F).hom.app _)
    ((isIso_iff_bijective _).mp inferInstance)
    (funext fun x ↦ (congrFun (congrArg (fun φ ↦ φ.hom.app (op T))
      (coefficientPullbackComparison_unit (smallEtaleBaseChange i) X.smallEtaleTopology
        Y.smallEtaleTopology (forget AddCommGrpCat.{u + 1}) F)) x).symm)

end Abelian

section Sets

variable {X Y : Scheme.{u}} (i : Y ⟶ X)

/-- If the comparison `Γ(X, G) → Γ(Y, i^{-1} G)` is an isomorphism for a sheaf of sets `G`,
then the unit of the inverse-image adjunction is bijective on sections over a terminal object. -/
theorem bijective_smallEtaleUnit_app_of_isIso {T : X.Etale} (hT : IsTerminal T)
    (G : Sheaf X.smallEtaleTopology (Type (u + 1)))
    [IsIso ((globalSectionsSmallEtaleInverseImage.{u, 0} i).app G)] :
    Function.Bijective
      (((smallEtaleInverseImageAdjunction.{u, 0} i).unit.app G).hom.app (op T)) := by
  have h1 : IsIso (G.ΓRes (op T)) :=
    G.isLimitConeΓ.isIso_π_app_of_isInitial (op T) (initialOpOfTerminal hT)
  have h2 : IsIso (((smallEtaleInverseImage.{u, 0} i).obj G).ΓRes
      (op ((smallEtaleBaseChange i).obj T))) :=
    ((smallEtaleInverseImage.{u, 0} i).obj G).isLimitConeΓ.isIso_π_app_of_isInitial _
      (initialOpOfTerminal (hT.isTerminalObj _))
  have : IsIso (smallEtaleUnitApp.{u, 0} i G T) := by
    have : IsIso (G.ΓRes (op T) ≫ smallEtaleUnitApp.{u, 0} i G T) := by
      rw [← globalSectionsSmallEtaleInverseImage_app_comp_ΓRes.{u, 0} i G T]
      infer_instance
    exact IsIso.of_isIso_comp_left (G.ΓRes (op T)) _
  exact (isIso_iff_bijective _).mp this

end Sets

section Restriction

variable {X Y : Scheme.{u}} (i : Y ⟶ X)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **Restriction in degree zero is bijective** for every abelian sheaf as soon as the
comparison of global sections of sheaves of sets is invertible, for instance when `i` is
universally submersive with geometrically connected fibres (Stacks Project Tag 0EZK). -/
theorem etaleCohomologyRestrictionMap_zero_bijective_of_isIso
    [IsIso (globalSectionsSmallEtaleInverseImage.{u, 0} i)]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, w} i F 0) := by
  rw [etaleCohomologyRestrictionMap_zero_bijective_iff_unit i terminalIsTerminal,
    bijective_etaleAbelianUnit_app_iff_set]
  exact bijective_smallEtaleUnit_app_of_isIso i terminalIsTerminal _

/-- **Restriction to a scalar extension over a separably closed field is bijective in degree
zero.** For `X` over a separably closed field `k` and any field extension `k'/k`, the map
`H^0(X, F) → H^0(X_{k'}, F|_{X_{k'}})` is bijective for every abelian sheaf `F`. -/
@[sga "4 XII 5.4" "(i), special case"]
theorem etaleCohomologyRestrictionMap_zero_bijective_of_isSepClosed
    (k k' : Type u) [Field k] [IsSepClosed k] [Field k'] [Algebra k k']
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{w} (Sheaf
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).smallEtaleTopology
      AddCommGrpCat.{u + 1})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, w}
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) F 0) := by
  have : GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k k'))) :=
    (AlgebraicGeometry.geometricallyConnected_spec_iff k k').2
      ((Algebra.isGeometricallyConnected_iff_connectedSpace_primeSpectrum k k').2 inferInstance)
  have : IsIso (globalSectionsSmallEtaleInverseImage.{u, 0}
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))) :=
    isIso_globalSectionsSmallEtaleInverseImage _ (universally_isQuotientMap_of_flat_quasiCompact _)
  exact etaleCohomologyRestrictionMap_zero_bijective_of_isIso _ F

end Restriction

end Stacks.EtaleCohomology

end
