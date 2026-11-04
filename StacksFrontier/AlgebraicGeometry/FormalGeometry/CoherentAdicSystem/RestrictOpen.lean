module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Transition
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic

/-!
# Restricting a coherent adic system along an open immersion

Let `f : Y ⟶ X` be an open immersion of schemes with `X` locally Noetherian, and let `ℐ` be a
quasi-coherent ideal sheaf on `X`. Restricting a coherent adic system `(F_n)` along `ℐ` term by
term produces a coherent adic system along `ℐ|_Y`, and this assignment is a functor
`Coh(X, ℐ) ⥤ Coh(Y, ℐ|_Y)`.

All three defining clauses survive restriction. Coherence does because restriction along an open
immersion is restriction to an open subscheme. The annihilation `ℐ ⁿ⁺¹ F_n = 0` does because the
scalar action on a section of `F_n|_Y` over an affine open `V` is the action of `Γ(X, f(V))` on
the same section through the isomorphism `Γ(X, f(V)) ≅ Γ(Y, V)`, under which `ℐ|_Y` is the
preimage of `ℐ`. The quotient clause does because restriction is a left adjoint, so it preserves
the cokernel presenting `F_n` as `F_{n+1} / ℐ ⁿ⁺¹ F_{n+1}`, and it carries the subsheaf
`ℐ ⁿ⁺¹ F_{n+1}` isomorphically onto `(ℐ|_Y) ⁿ⁺¹ (F_{n+1}|_Y)`.

## Main definitions

* `Stacks.Algebraization.restrictIdealPowerQuotientIso` — the identification of
  `(M / ℐ ⁿ M)|_Y` with `M|_Y / (ℐ|_Y) ⁿ (M|_Y)`.
* `Stacks.Coherent.restrictFunctor` — the restriction functor `Coh(X, ℐ) ⥤ Coh(Y, ℐ|_Y)`.
* `Stacks.Coherent.restrictFunctorOpen` — the same for the inclusion of an open subscheme.
* `Stacks.Coherent.restrictFunctorCompιIso` — composing it with the inclusion of the full
  subcategory is termwise restriction.

## Main results

* `Stacks.Algebraization.idealPowerMultiple_restrict_eq_bot` — a module annihilated by `ℐ ⁿ`
  restricts to a module annihilated by `(ℐ|_Y) ⁿ`.
* `Stacks.Coherent.isCoherentAdicSystem_restrict` — the termwise restriction of a coherent adic
  system along `ℐ` is a coherent adic system along `ℐ|_Y`.
* `Stacks.Coherent.restrictFunctor_obj_obj` — the terms of the restricted system are the
  restricted terms, and `Stacks.Coherent.restrictFunctor_map_hom_app` — the restricted morphism
  acts on terms as the restriction of its components.
* `Stacks.Coherent.isIso_of_isIso_restrictFunctor_map_system` — invertibility in `Coh(X, ℐ)` is
  local on `X`: it suffices that the restriction to each member of an open covering be
  invertible.

## Implementation notes

The functor is built as `CategoryTheory.ObjectProperty.lift` of the composite of the inclusion of
`Coh(X, ℐ)` with `(Functor.whiskeringRight _ _ _).obj (Scheme.Modules.restrictFunctor f)`, so its
action on morphisms is whiskering on the nose; additivity and preservation of zero morphisms are
then the instances Mathlib already has for a lift of an additive functor.

The restriction functor is stated for an arbitrary open immersion rather than for the inclusion
of an open subscheme, which is the generality the algebraization arguments use: there the
morphism is an inclusion `V.ι` composed into `X` and is not presented as an inclusion of an open
of the base. `Stacks.Coherent.restrictFunctorOpen` recovers the special case.

## References

* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u v

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

/-- Restriction along an open immersion preserves annihilation by a power of an ideal sheaf:
if `ℐ ⁿ M` vanishes then so does `(ℐ|_Y) ⁿ (M|_Y)`.

Over an affine open `V ⊆ Y` the ideal of `ℐ|_Y` is the preimage of the ideal of `ℐ` over `f(V)`,
and the scalar action on the sections of `M|_Y` is the action on the sections of `M` over `f(V)`
through the same isomorphism of rings. -/
public theorem idealPowerMultiple_restrict_eq_bot {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (I : X.IdealSheafData) (n : ℕ) (M : X.Modules)
    (h : idealPowerMultiple I n M = ⊥) :
    idealPowerMultiple (I.comap f) n ((Scheme.Modules.restrictFunctor f).obj M) = ⊥ := by
  have hsec : ∀ W : X.affineOpens,
      I.ideal W ^ n • (⊤ : Submodule Γ(X, W.1) Γ(M, W.1)) ≤ ⊥ := by
    intro W
    have hgen := (idealPowerMultiple_le_iff I n M (idealPowerMultiple I n M)).mp le_rfl W
    rw [h] at hgen
    exact hgen.trans (le_of_eq (SheafOfModules.Submodule.bot_obj M (op W.1)))
  refine le_antisymm ((idealPowerMultiple_le_iff (I.comap f) n _ ⊥).2 fun V => ?_) bot_le
  refine Submodule.smul_le.2 fun a ha x _ => ?_
  have ha' : (f.appIso V.1).inv a ∈
      I.ideal ⟨f ''ᵁ V.1, V.2.image_of_isOpenImmersion f⟩ ^ n := by
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at ha
    exact Ideal.le_comap_pow _ n ha
  have hzero : (f.appIso V.1).inv a • (M.restrictAppIso f V.1).hom x = 0 :=
    (Submodule.mem_bot _).1 (hsec ⟨f ''ᵁ V.1, V.2.image_of_isOpenImmersion f⟩
      (Submodule.smul_mem_smul ha' Submodule.mem_top))
  have hax : a • x = 0 :=
    (M.restrictAppIso f V.1).addCommGroupIsoToAddEquiv.injective
      ((Scheme.Modules.smul_restrictAppIso_hom_apply f M V.1 a x).trans
        (hzero.trans (map_zero (M.restrictAppIso f V.1).addCommGroupIsoToAddEquiv).symm))
  rw [hax]
  exact Submodule.zero_mem _

/-- Restriction along an open immersion carries the inclusion of `ℐ ⁿ M` to the inclusion of
`(ℐ|_Y) ⁿ (M|_Y)`, through the comparison map
`Stacks.Algebraization.idealPowerMultipleRestrictMap`. -/
public theorem restrictFunctor_map_idealPowerMultiple_ι {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (I : X.IdealSheafData) (n : ℕ) (M : X.Modules) [M.IsQuasicoherent] :
    (Scheme.Modules.restrictFunctor f).map (idealPowerMultiple I n M).ι =
      idealPowerMultipleRestrictMap f I n M ≫
        (idealPowerMultiple (I.comap f) n ((Scheme.Modules.restrictFunctor f).obj M)).ι := by
  ext W x
  rfl

/-- **Restriction commutes with the ideal-power quotient.** For an open immersion `f : Y ⟶ X`
and a quasi-coherent `𝒪_X`-module `M`, restricting `M / ℐ ⁿ M` to `Y` gives
`M|_Y / (ℐ|_Y) ⁿ (M|_Y)`.

Restriction is a left adjoint, hence preserves the cokernel, and it carries `ℐ ⁿ M`
isomorphically onto `(ℐ|_Y) ⁿ (M|_Y)`. -/
public def restrictIdealPowerQuotientIso {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (I : X.IdealSheafData) (n : ℕ) (M : X.Modules) [M.IsQuasicoherent] :
    idealPowerQuotient (I.comap f) n ((Scheme.Modules.restrictFunctor f).obj M) ≅
      (Scheme.Modules.restrictFunctor f).obj (idealPowerQuotient I n M) :=
  haveI := isIso_idealPowerMultipleRestrictMap f I n M
  (PreservesCokernel.iso (Scheme.Modules.restrictFunctor f) (idealPowerMultiple I n M).ι ≪≫
    cokernel.mapIso ((Scheme.Modules.restrictFunctor f).map (idealPowerMultiple I n M).ι)
      (idealPowerMultiple (I.comap f) n ((Scheme.Modules.restrictFunctor f).obj M)).ι
      (asIso (idealPowerMultipleRestrictMap f I n M))
      (Iso.refl ((Scheme.Modules.restrictFunctor f).obj M))
      (restrictFunctor_map_idealPowerMultiple_ι f I n M)).symm

/-- The identification of the restricted quotient intertwines the two quotient projections. -/
public theorem cokernel_π_comp_restrictIdealPowerQuotientIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (I : X.IdealSheafData) (n : ℕ) (M : X.Modules) [M.IsQuasicoherent] :
    cokernel.π (idealPowerMultiple (I.comap f) n
        ((Scheme.Modules.restrictFunctor f).obj M)).ι ≫
      (restrictIdealPowerQuotientIso f I n M).hom =
      (Scheme.Modules.restrictFunctor f).map
        (cokernel.π (idealPowerMultiple I n M).ι) := by
  have := isIso_idealPowerMultipleRestrictMap f I n M
  set R := Scheme.Modules.restrictFunctor f
  set e : R.obj (idealPowerQuotient I n M) ≅
      idealPowerQuotient (I.comap f) n (R.obj M) :=
    PreservesCokernel.iso R (idealPowerMultiple I n M).ι ≪≫
      cokernel.mapIso (R.map (idealPowerMultiple I n M).ι)
        (idealPowerMultiple (I.comap f) n (R.obj M)).ι
        (asIso (idealPowerMultipleRestrictMap f I n M)) (Iso.refl (R.obj M))
        (restrictFunctor_map_idealPowerMultiple_ι f I n M)
  have key : R.map (cokernel.π (idealPowerMultiple I n M).ι) ≫ e.hom =
      cokernel.π (idealPowerMultiple (I.comap f) n (R.obj M)).ι :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ (cokernel.mapIso (R.map (idealPowerMultiple I n M).ι)
            (idealPowerMultiple (I.comap f) n (R.obj M)).ι
            (asIso (idealPowerMultipleRestrictMap f I n M)) (Iso.refl (R.obj M))
            (restrictFunctor_map_idealPowerMultiple_ι f I n M)).hom)
          (PreservesCokernel.π_iso_hom R (idealPowerMultiple I n M).ι)).trans
        ((cokernelπ_map _ _ _ _ (restrictFunctor_map_idealPowerMultiple_ι f I n M)).trans
          (Category.id_comp _)))
  exact (congrArg (fun z => z ≫ e.inv) key.symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun z => R.map (cokernel.π (idealPowerMultiple I n M).ι) ≫ z)
        e.hom_inv_id).trans (Category.comp_id _)))

end Stacks.Algebraization

namespace Stacks.Coherent

open Stacks.Algebraization

/-- **The termwise restriction of a coherent adic system is a coherent adic system.** For an
open immersion `f : Y ⟶ X` of schemes with `X` locally Noetherian, restricting a coherent adic
system along `ℐ` term by term gives a coherent adic system along `ℐ|_Y`. -/
public theorem isCoherentAdicSystem_restrict {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (F : CoherentAdicSystems I) :
    IsCoherentAdicSystem (I.comap f)
      (F.obj ⋙ Scheme.Modules.restrictFunctor f) := by
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_⟩
  · exact @isCoherent_restrict_of_isOpenImmersion X Y f ‹_› ‹_› (F.obj.obj (op n))
      (F.property.isCoherent n)
  · exact idealPowerMultiple_restrict_eq_bot f I (n + 1) (F.obj.obj (op n))
      (F.property.idealPowerMultiple_eq_bot n)
  · have : (F.obj.obj (op (n + 1))).IsQuasicoherent := F.property.isQuasicoherent (n + 1)
    refine ⟨restrictIdealPowerQuotientIso f I (n + 1) (F.obj.obj (op (n + 1))) ≪≫
      (Scheme.Modules.restrictFunctor f).mapIso (F.property.quotientIso n), ?_⟩
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ (Scheme.Modules.restrictFunctor f).map
            (F.property.quotientIso n).hom)
          (cokernel_π_comp_restrictIdealPowerQuotientIso f I (n + 1)
            (F.obj.obj (op (n + 1))))).trans
        (((Scheme.Modules.restrictFunctor f).map_comp _ _).symm.trans
          (congrArg (Scheme.Modules.restrictFunctor f).map
            (F.property.cokernel_π_comp_quotientIso n))))

/-- **Restriction of coherent adic systems along an open immersion.** For an open immersion
`f : Y ⟶ X` of schemes with `X` locally Noetherian, termwise restriction is a functor
`Coh(X, ℐ) ⥤ Coh(Y, ℐ|_Y)`. -/
public def restrictFunctor {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)
    {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] :
    CoherentAdicSystems I ⥤ CoherentAdicSystems (I.comap f) :=
  ObjectProperty.lift (IsCoherentAdicSystem (I.comap f))
    (ObjectProperty.ι (IsCoherentAdicSystem I) ⋙
      (Functor.whiskeringRight _ _ _).obj (Scheme.Modules.restrictFunctor f))
    (isCoherentAdicSystem_restrict I f)

/-- Restriction of coherent adic systems to an open subscheme. -/
public abbrev restrictFunctorOpen {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (U : X.Opens) :
    CoherentAdicSystems I ⥤ CoherentAdicSystems (I.comap U.ι) :=
  restrictFunctor I U.ι

/-- The terms of a restricted coherent adic system are the restricted terms. -/
public theorem restrictFunctor_obj_obj {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (F : CoherentAdicSystems I) (n : ℕᵒᵖ) :
    ((restrictFunctor I f).obj F).obj.obj n =
      (Scheme.Modules.restrictFunctor f).obj (F.obj.obj n) :=
  rfl

/-- The restriction functor is additive: its action on morphisms is whiskering with the additive
functor `AlgebraicGeometry.Scheme.Modules.restrictFunctor`. -/
public instance restrictFunctor_additive {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] :
    (restrictFunctor I f).Additive :=
  inferInstanceAs (ObjectProperty.lift (IsCoherentAdicSystem (I.comap f))
    (ObjectProperty.ι (IsCoherentAdicSystem I) ⋙
      (Functor.whiskeringRight _ _ _).obj (Scheme.Modules.restrictFunctor f))
    (isCoherentAdicSystem_restrict I f)).Additive

/-- The restriction functor preserves zero morphisms, being additive. -/
public instance restrictFunctor_preservesZeroMorphisms {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] :
    (restrictFunctor I f).PreservesZeroMorphisms :=
  inferInstance

/-- Composing the restriction functor with the inclusion of the full subcategory of coherent
adic systems is termwise restriction. -/
public def restrictFunctorCompιIso {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] :
    restrictFunctor I f ⋙ ObjectProperty.ι (IsCoherentAdicSystem (I.comap f)) ≅
      ObjectProperty.ι (IsCoherentAdicSystem I) ⋙
        (Functor.whiskeringRight _ _ _).obj (Scheme.Modules.restrictFunctor f) :=
  ObjectProperty.liftCompιIso _ _ (isCoherentAdicSystem_restrict I f)

/-- The restriction of a morphism of coherent adic systems acts on terms as the restriction of
its components. -/
public theorem restrictFunctor_map_hom_app {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    {F G : CoherentAdicSystems I} (α : F ⟶ G) (n : ℕᵒᵖ) :
    ((restrictFunctor I f).map α).hom.app n =
      (Scheme.Modules.restrictFunctor f).map (α.hom.app n) :=
  rfl

/-- **Invertibility in `Coh(X, ℐ)` is local on `X`.** A morphism of coherent adic systems whose
restriction to each member of an open covering is invertible is invertible. -/
public theorem isIso_of_isIso_restrictFunctor_map_system {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) {F G : CoherentAdicSystems I} (α : F ⟶ G)
    {J : Type v} (U : J → X.Opens) (hU : IsOpenCover U)
    (h : ∀ j, IsIso ((restrictFunctor I (U j).ι).map α)) : IsIso α := by
  rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
  intro n
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict
    (α.hom.app n) U hU fun j => ?_
  have hj : IsIso (((restrictFunctor I (U j).ι).map α).hom) :=
    (ObjectProperty.isIso_hom_iff _).mpr (h j)
  rw [NatTrans.isIso_iff_isIso_app] at hj
  exact (restrictFunctor_map_hom_app I (U j).ι α n) ▸ hj n

end Stacks.Coherent

end
