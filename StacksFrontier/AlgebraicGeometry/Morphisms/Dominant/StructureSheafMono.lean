module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# The structure sheaf of the target embeds in a dominant direct image

Let `h : A ⟶ B` be a morphism of schemes. Pushing the structure sheaf of `A` forward along `h`
and comparing it with the structure sheaf of `B` gives a morphism `𝒪_B ⟶ h_* 𝒪_A` of
`𝒪_B`-modules, whose action on the sections over an open `U` is the ring map `h.app U`. If `h`
is quasi-compact with vanishing kernel ideal sheaf then those ring maps are injective, and this
file concludes that `𝒪_B ⟶ h_* 𝒪_A` is a monomorphism.

## Main results

* `AlgebraicGeometry.Scheme.Hom.app_unitToPushforwardObjUnit`: on sections over an open `U` the
  morphism `𝒪_B ⟶ h_* 𝒪_A` is the ring map `h.app U`.
* `AlgebraicGeometry.Scheme.Hom.mono_unitToPushforwardObjUnit_of_app_injective`: a morphism of
  schemes injective on sections over every open has `𝒪_B ⟶ h_* 𝒪_A` a monomorphism.
* `AlgebraicGeometry.Scheme.Hom.injective_app_unitToPushforwardObjUnit` and
  `AlgebraicGeometry.Scheme.Hom.mono_unitToPushforwardObjUnit`: for a quasi-compact
  scheme-theoretically dominant morphism, `𝒪_B ⟶ h_* 𝒪_A` is injective on sections over every
  open and hence a monomorphism of `𝒪_B`-modules.
* `AlgebraicGeometry.Scheme.Hom.mono_pushforward_map_unitToPushforwardObjUnit`: that
  monomorphism survives a further direct image, giving `g_* 𝒪_B ⟶ (h ≫ g)_* 𝒪_A` monic for any
  `g : B ⟶ S`.
* `AlgebraicGeometry.Scheme.Hom.exists_mono_pushforward_unit_of_comp_eq`: the same conclusion
  presented at a factorization `h ≫ g = p`, which is the form a dominant factorization through
  an intermediate scheme is used in.

## Implementation notes

The morphism is Mathlib's `SheafOfModules.unitToPushforwardObjUnit` applied to the morphism of
sheaves of rings `AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom` underlying `h`; no new
definition is introduced, so these results apply to every spelling of that map in this library.

`AlgebraicGeometry.Scheme.Modules` is a `def`, so the category of `𝒪_B`-modules and the category
of sheaves of modules over `B.ringCatSheaf` are two `Category` instances on one type, and an
instance of `CategoryTheory.Mono` for one is not found by instance search for the other. The
conclusions are therefore pinned to the `𝒪_B`-module spelling with `Mono (C := B.Modules)`,
which is the one a consumer of a monomorphism of `𝒪_B`-modules uses; a term of that type still
serves the sheaf-of-modules spelling, where the two agree definitionally.

Monicity is detected on the underlying abelian presheaf: `Scheme.Modules.toPresheaf` is faithful
and a natural transformation of presheaves is a monomorphism as soon as each of its components
is, which for abelian groups is injectivity.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {A B : Scheme.{u}} (h : A ⟶ B)

/-- The morphism `𝒪_B ⟶ h_* 𝒪_A` of `𝒪_B`-modules acts on the sections over an open `U` as the
ring map `h.app U`. -/
@[simp]
theorem app_unitToPushforwardObjUnit (U : B.Opens) (a : Γ(B, U)) :
    Modules.Hom.app (SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom) U a =
      h.app U a :=
  rfl

/-- A morphism of schemes which is injective on the sections over every open has
`𝒪_B ⟶ h_* 𝒪_A` a monomorphism of `𝒪_B`-modules. -/
theorem mono_unitToPushforwardObjUnit_of_app_injective
    (hh : ∀ U : B.Opens, Function.Injective (h.app U)) :
    Mono (C := B.Modules) (SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom) := by
  have hmono : ∀ U, Mono (((Modules.toPresheaf B).map
      (SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom)).app U) := by
    intro U
    rw [AddCommGrpCat.mono_iff_injective]
    intro s t hst
    exact hh U.unop hst
  exact (Modules.toPresheaf B).mono_of_mono_map (NatTrans.mono_of_mono_app _)

variable [IsSchemeTheoreticallyDominant h] [QuasiCompact h]

/-- For a quasi-compact scheme-theoretically dominant morphism, `𝒪_B ⟶ h_* 𝒪_A` is injective on
the sections over every open: that map is the ring map `h.app U`, which is injective because the
kernel ideal sheaf of `h` vanishes. -/
theorem injective_app_unitToPushforwardObjUnit (U : B.Opens) :
    Function.Injective
      (Modules.Hom.app (SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom) U) :=
  h.app_injective U

/-- **A quasi-compact scheme-theoretically dominant morphism embeds the structure sheaf of its
target into the direct image of the structure sheaf of its source**: the morphism
`𝒪_B ⟶ h_* 𝒪_A` of `𝒪_B`-modules is a monomorphism. -/
theorem mono_unitToPushforwardObjUnit :
    Mono (C := B.Modules) (SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom) :=
  h.mono_unitToPushforwardObjUnit_of_app_injective fun U ↦ h.app_injective U

/-- The components of the forward map of a natural isomorphism are monomorphisms. -/
private theorem mono_hom_app_of_iso {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (e : F ≅ G) (X : C) : Mono (e.hom.app X) :=
  @IsIso.mono_of_iso _ _ _ _ _ (NatIso.hom_app_isIso _ _)

/-- **The embedding of structure sheaves stays a monomorphism after a further direct image.**
For `g : B ⟶ S` arbitrary, the comparison `g_* 𝒪_B ⟶ (h ≫ g)_* 𝒪_A` of `𝒪_S`-modules is a
monomorphism, since `g_*` is a right adjoint and so preserves monomorphisms. -/
theorem mono_pushforward_map_unitToPushforwardObjUnit {S : Scheme.{u}} (g : B ⟶ S) :
    Mono (C := S.Modules) ((Modules.pushforward g).map
        (SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom) ≫
      (Modules.pushforwardComp h g).hom.app (SheafOfModules.unit.{u} A.ringCatSheaf)) :=
  have hmap : Mono (C := S.Modules) ((Modules.pushforward g).map
      (SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom)) :=
    @Functor.map_mono _ _ _ _ (Modules.pushforward g) inferInstance _ _ _
      h.mono_unitToPushforwardObjUnit
  @mono_comp _ _ _ _ _ _ hmap _ (mono_hom_app_of_iso _ _)

/-- **A dominant factorization embeds the structure sheaf of the intermediate scheme.** If
`h : A ⟶ B` is quasi-compact and scheme-theoretically dominant and `h ≫ g = p`, then `g_* 𝒪_B`
is a submodule of `p_* 𝒪_A` as an `𝒪_S`-module. -/
theorem exists_mono_pushforward_unit_of_comp_eq {S : Scheme.{u}} (g : B ⟶ S) (p : A ⟶ S)
    (hp : h ≫ g = p) :
    ∃ φ : (Modules.pushforward g).obj (SheafOfModules.unit.{u} B.ringCatSheaf) ⟶
        (Modules.pushforward p).obj (SheafOfModules.unit.{u} A.ringCatSheaf),
      Mono (C := S.Modules) φ :=
  ⟨_, @mono_comp _ _ _ _ _ _ (h.mono_pushforward_map_unitToPushforwardObjUnit g) _
    (mono_hom_app_of_iso (Modules.pushforwardCongr hp) _)⟩

end AlgebraicGeometry.Scheme.Hom

end
