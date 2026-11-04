module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint

/-!
# Pushforward of sheaves of modules along a dense subsite and a ring isomorphism

Let `F : C ⥤ D` exhibit `(C, J)` as a dense subsite of `(D, K)`, `R` a sheaf of rings on `D` and
`φ : S ≅ F^*R` an isomorphism of sheaves of rings on `C`. The pushforward
`SheafOfModules.pushforward φ.hom` of sheaves of `R`-modules to sheaves of `S`-modules is
restriction to the dense subsite followed by restriction of scalars along `φ`, hence fully
faithful, and essentially surjective when restriction of sheaves is an equivalence.

## Main definitions

* `SheafOfModules.pushforwardRestrictScalarsIso`: pushforward commutes with restriction of scalars
  along a commutative square of sheaves of rings.

## Main results

* `SheafOfModules.pushforwardIsoModuleRestriction`: the factorisation.
* `SheafOfModules.full_pushforward_of_iso`, `SheafOfModules.faithful_pushforward_of_iso`,
  `SheafOfModules.essSurj_pushforward_of_iso`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe w v₁ v₂ u₁ u₂

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} (F : C ⥤ D) [F.IsDenseSubsite J K]
  {S : Sheaf J RingCat.{w}} {R : Sheaf K RingCat.{w}}
  (φ : S ≅ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R)

/-- The pushforward along a dense subsite and a ring isomorphism is restriction to the subsite
followed by restriction of scalars. -/
def pushforwardIsoModuleRestriction :
    pushforward.{w} φ.hom ≅
      Stacks.DenseSubsiteModules.moduleRestriction J K F R ⋙
        (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso φ.symm).functor :=
  Iso.refl _

/-- Pushforward along a dense subsite and a ring isomorphism is full. -/
theorem full_pushforward_of_iso : (pushforward.{w} φ.hom).Full :=
  Functor.Full.of_iso (pushforwardIsoModuleRestriction F φ).symm

/-- Pushforward along a dense subsite and a ring isomorphism is faithful. -/
theorem faithful_pushforward_of_iso : (pushforward.{w} φ.hom).Faithful :=
  Functor.Faithful.of_iso (pushforwardIsoModuleRestriction F φ).symm

/-- Pushforward along a dense subsite inducing an equivalence of sheaf categories and a ring
isomorphism is essentially surjective. -/
theorem essSurj_pushforward_of_iso
    [(F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsEquivalence] :
    (pushforward.{w} φ.hom).EssSurj :=
  have := (Stacks.DenseSubsiteModules.moduleRestrictionEquivalence J K F R).isEquivalence_functor
  Functor.essSurj_of_iso (pushforwardIsoModuleRestriction F φ).symm

/-! ### Pushforward commutes with restriction of scalars -/

section Square

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  [F.IsContinuous J K] {O A : Sheaf K RingCat.{w}} {O' A' : Sheaf J RingCat.{w}}
  (a : A ⟶ O) (a' : A' ⟶ O')
  (ω : O' ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj O)
  (α : A' ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj A)
  (comm : a' ≫ ω = α ≫ (F.sheafPushforwardContinuous RingCat.{w} J K).map a)

include comm in
/-- **Pushforward commutes with restriction of scalars**: for a square of sheaves of rings
`a' ≫ ω = α ≫ F^*a`, pushing an `O`-module forward along `ω` and restricting scalars along `a'`
is restricting along `a` and pushing forward along `α`. Both have the sections of the module over
the objects `F(U)`, with `A'` acting through the two equal composites. -/
def pushforwardRestrictScalarsIso :
    pushforward.{w} ω ⋙ restrictScalars a' ≅ restrictScalars a ⋙ pushforward.{w} α :=
  NatIso.ofComponents (fun M => (fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U => (AddEquiv.toLinearEquiv
      (M := ↑(((pushforward.{w} ω ⋙ restrictScalars a').obj M).val.obj U))
      (M₂ := ↑(((restrictScalars a ⋙ pushforward.{w} α).obj M).val.obj U))
      (AddEquiv.refl _) (fun r x => by
        have h : (show O.obj.obj (Opposite.op (F.obj U.unop)) from
              (ω.hom.app U).hom ((a'.hom.app U).hom r)) =
            (a.hom.app (Opposite.op (F.obj U.unop))).hom ((α.hom.app U).hom r) :=
          congrArg (fun φ => (φ.hom.app U).hom r) comm
        change (show O.obj.obj (Opposite.op (F.obj U.unop)) from
              (ω.hom.app U).hom ((a'.hom.app U).hom r)) •
            (show M.val.obj (Opposite.op (F.obj U.unop)) from x) =
          (a.hom.app (Opposite.op (F.obj U.unop))).hom ((α.hom.app U).hom r) •
            (show M.val.obj (Opposite.op (F.obj U.unop)) from x)
        rw [h])).toModuleIso)
      fun _ _ _ => rfl)) fun _ => rfl

/-- On sections, the hom of `pushforwardRestrictScalarsIso` is the identity. -/
@[simp]
theorem pushforwardRestrictScalarsIso_hom_app_val_app (M : SheafOfModules.{w} O) (U : Cᵒᵖ) (x) :
    ((pushforwardRestrictScalarsIso a a' ω α comm).hom.app M).val.app U x = x :=
  rfl

/-- On sections, the inverse of `pushforwardRestrictScalarsIso` is the identity. -/
@[simp]
theorem pushforwardRestrictScalarsIso_inv_app_val_app (M : SheafOfModules.{w} O) (U : Cᵒᵖ) (x) :
    ((pushforwardRestrictScalarsIso a a' ω α comm).inv.app M).val.app U x = x :=
  rfl

/-- Pushing forward a map into a module with restricted scalars and commuting the restrictions:
on sections, the map itself. -/
theorem pushforward_map_comp_pushforwardRestrictScalarsIso_inv_app_val_app
    {I : SheafOfModules.{w} A} {N : SheafOfModules.{w} O} (c : I ⟶ (restrictScalars a).obj N)
    (U : Cᵒᵖ) (y : ((pushforward.{w} α).obj I).val.obj U) :
    ((pushforward.{w} α).map c ≫ (pushforwardRestrictScalarsIso a a' ω α comm).inv.app N).val.app
      U y = c.val.app (F.op.obj U) y :=
  rfl

end Square

end SheafOfModules
