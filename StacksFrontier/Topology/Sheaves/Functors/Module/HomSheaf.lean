module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Sites.SheafHom
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.RestrictScalarsCoextension
public import StacksFrontier.Topology.Sheaves.Sheaf.Module
import StacksCore.Tactic.StacksAttribute

/-!
# The internal Hom sheaf, and its adjunction with restriction of scalars

Let `α : 𝒪₁ ⟶ 𝒪₂` be a homomorphism of sheaves of rings on a site `(C, J)`. For an
`𝒪₁`-module `F` the internal Hom `SheafHom_{𝒪₁}(𝒪₂, F)` is the sheaf whose sections over an
object `U` are the morphisms `𝒪₂|_U ⟶ F|_U` of `𝒪₁|_U`-modules on the slice `Over U`. Right
multiplication in `𝒪₂` makes it an `𝒪₂`-module, and the resulting functor is right adjoint to
restriction of scalars along `α`.

## Main definitions

* `RingedSpaceModuleAdjunction.homSheafObj` is the internal Hom sheaf `SheafHom_{𝒪₁}(𝒪₂, F)`,
  as a sheaf of `𝒪₂`-modules.
* `RingedSpaceModuleAdjunction.homSheaf` is the functor `F ↦ SheafHom_{𝒪₁}(𝒪₂, F)`.

## Main results

* `RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction`: restriction of scalars along `α`
  is left adjoint to `homSheaf α`.

## References

* [Stacks Project, Tag 0A6F](https://stacks.math.columbia.edu/tag/0A6F)
* [Stacks Project, Tag 0932](https://stacks.math.columbia.edu/tag/0932)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace RingedSpaceModuleAdjunction

/-- On underlying presheaves of abelian groups, the hom of the slice-restriction isomorphism
`Stacks.PresheafOfModules.CoextendScalars.overRestrictIso` is the identity. -/
private theorem toPresheaf_map_overRestrictIso_hom {C : Type u} [Category.{u} C]
    {O : Cᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{u} O) {U V : C} (g : V ⟶ U) :
    (PresheafOfModules.toPresheaf ((Over.forget V).op ⋙ O)).map
        (Stacks.PresheafOfModules.CoextendScalars.overRestrictIso V U g M).hom =
      𝟙 ((PresheafOfModules.toPresheaf ((Over.forget V).op ⋙ O)).obj
        (Stacks.PresheafOfModules.CoextendScalars.restrictToOver V M)) := by
  simp only [Stacks.PresheafOfModules.CoextendScalars.overRestrictIso, eqToIso.hom, eqToHom_map]
  exact eqToHom_refl _ _

/-- On underlying presheaves of abelian groups, the inverse of the slice-restriction isomorphism
`Stacks.PresheafOfModules.CoextendScalars.overRestrictIso` is the identity. -/
private theorem toPresheaf_map_overRestrictIso_inv {C : Type u} [Category.{u} C]
    {O : Cᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{u} O) {U V : C} (g : V ⟶ U) :
    (PresheafOfModules.toPresheaf ((Over.forget V).op ⋙ O)).map
        (Stacks.PresheafOfModules.CoextendScalars.overRestrictIso V U g M).inv =
      𝟙 ((PresheafOfModules.toPresheaf ((Over.forget V).op ⋙ O)).obj
        (Stacks.PresheafOfModules.CoextendScalars.restrictToOver V M)) := by
  simp only [Stacks.PresheafOfModules.CoextendScalars.overRestrictIso, eqToIso.inv, eqToHom_map]
  exact eqToHom_refl _ _

/-- `PresheafOfModules.map_smul` for the underlying presheaf of abelian groups: its restriction
maps are semilinear along the restriction maps of the base ring. -/
@[sga "3 I 6.4" "more general"]
private theorem presheaf_map_smul {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    (M : PresheafOfModules.{u} R) {Y Z : Cᵒᵖ} (f : Y ⟶ Z) (r : R.obj Y) (m : M.presheaf.obj Y) :
    M.presheaf.map f (r • m) = R.map f r • M.presheaf.map f m :=
  M.map_smul f r m

private noncomputable abbrev coextPresheafHom
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {𝒪₁ 𝒪₂ : CategoryTheory.Sheaf J RingCat.{u}}
    (α : 𝒪₁ ⟶ 𝒪₂) (F : SheafOfModules.{u} 𝒪₁) :=
  CategoryTheory.presheafHom (Stacks.PresheafOfModules.CoextendScalars.O'asOModule α.hom).presheaf
    F.val.presheaf

private noncomputable def coextUnderlying
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {𝒪₁ 𝒪₂ : CategoryTheory.Sheaf J RingCat.{u}}
    (α : 𝒪₁ ⟶ 𝒪₂) (F : SheafOfModules.{u} 𝒪₁) (U : C)
    (ψ : Stacks.PresheafOfModules.CoextendScalars.coextSec α.hom F.val (Opposite.op U)) :
    (coextPresheafHom α F).obj (Opposite.op U) :=
  (PresheafOfModules.toPresheaf ((Over.forget U).op ⋙ 𝒪₁.obj)).map ψ

/-- Passing to underlying morphisms of presheaves of abelian groups commutes with restriction:
`Stacks.PresheafOfModules.CoextendScalars.coextRestrFun` corresponds to restriction in
`CategoryTheory.presheafHom`. -/
private theorem coextUnderlying_restr
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {𝒪₁ 𝒪₂ : CategoryTheory.Sheaf J RingCat.{u}}
    (α : 𝒪₁ ⟶ 𝒪₂) (F : SheafOfModules.{u} 𝒪₁) {U V : C} (g : V ⟶ U)
    (ψ : Stacks.PresheafOfModules.CoextendScalars.coextSec α.hom F.val (Opposite.op U)) :
    (coextPresheafHom α F).map g.op (coextUnderlying α F U ψ) =
      coextUnderlying α F V (Stacks.PresheafOfModules.CoextendScalars.coextRestrFun α.hom F.val g.op
        ψ) := by
  show Functor.whiskerLeft (Over.map g).op
      ((PresheafOfModules.toPresheaf ((Over.forget U).op ⋙ 𝒪₁.obj)).map ψ) =
    (PresheafOfModules.toPresheaf ((Over.forget V).op ⋙ 𝒪₁.obj)).map
      ((Stacks.PresheafOfModules.CoextendScalars.overRestrictIso V U g
        (Stacks.PresheafOfModules.CoextendScalars.O'asOModule α.hom)).inv ≫
        (Stacks.PresheafOfModules.CoextendScalars.overRestrictFunctor V U g).map ψ ≫
          (Stacks.PresheafOfModules.CoextendScalars.overRestrictIso V U g F.val).hom)
  rw [Functor.map_comp, Functor.map_comp, toPresheaf_map_overRestrictIso_inv,
    toPresheaf_map_overRestrictIso_hom]
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

private theorem coextRestrFun_comp
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {𝒪₁ 𝒪₂ : CategoryTheory.Sheaf J RingCat.{u}}
    (α : 𝒪₁ ⟶ 𝒪₂) (F : SheafOfModules.{u} 𝒪₁) {U V W : C}
    (g : W ⟶ V) (f : V ⟶ U) (ψ : Stacks.PresheafOfModules.CoextendScalars.coextSec α.hom F.val
      (Opposite.op U)) :
    Stacks.PresheafOfModules.CoextendScalars.coextRestrFun α.hom F.val (g ≫ f).op ψ =
      Stacks.PresheafOfModules.CoextendScalars.coextRestrFun α.hom F.val g.op
        (Stacks.PresheafOfModules.CoextendScalars.coextRestrFun α.hom F.val f.op ψ) := by
  apply (PresheafOfModules.toPresheaf ((Over.forget W).op ⋙ 𝒪₁.obj)).map_injective
  show coextUnderlying α F W
      (Stacks.PresheafOfModules.CoextendScalars.coextRestrFun α.hom F.val (g ≫ f).op ψ) =
    coextUnderlying α F W
      (Stacks.PresheafOfModules.CoextendScalars.coextRestrFun α.hom F.val g.op
        (Stacks.PresheafOfModules.CoextendScalars.coextRestrFun α.hom F.val f.op ψ))
  rw [← coextUnderlying_restr α F (g ≫ f) ψ,
    ← coextUnderlying_restr α F g (Stacks.PresheafOfModules.CoextendScalars.coextRestrFun α.hom
      F.val f.op ψ),
    ← coextUnderlying_restr α F f ψ, op_comp, Functor.map_comp_apply]

private def coextCompatible
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {𝒪₁ 𝒪₂ : CategoryTheory.Sheaf J RingCat.{u}}
    (α : 𝒪₁ ⟶ 𝒪₂) (F : SheafOfModules.{u} 𝒪₁) {U : C}
    (S : (J).Cover U)
    (φ : ∀ I : S.Arrow, Stacks.PresheafOfModules.CoextendScalars.coextSec α.hom F.val (Opposite.op
      I.Y)) : Prop :=
  ∀ ⦃I₁ I₂ : S.Arrow⦄ (r : I₁.Relation I₂),
    Stacks.PresheafOfModules.CoextendScalars.coextRestrFun α.hom F.val r.g₁.op (φ I₁) =
      Stacks.PresheafOfModules.CoextendScalars.coextRestrFun α.hom F.val r.g₂.op (φ I₂)

private noncomputable def coextRestrictToCover
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {𝒪₁ 𝒪₂ : CategoryTheory.Sheaf J RingCat.{u}}
    (α : 𝒪₁ ⟶ 𝒪₂) (F : SheafOfModules.{u} 𝒪₁) {U : C}
    (S : (J).Cover U)
    (ψ : Stacks.PresheafOfModules.CoextendScalars.coextSec α.hom F.val (Opposite.op U)) :
    {φ : ∀ I : S.Arrow, Stacks.PresheafOfModules.CoextendScalars.coextSec α.hom F.val (Opposite.op
      I.Y) //
      coextCompatible α F S φ} :=
  ⟨fun I => Stacks.PresheafOfModules.CoextendScalars.coextRestrFun α.hom F.val I.f.op ψ, by
    intro I₁ I₂ r
    rw [← coextRestrFun_comp α F r.g₁ I₁.f, ← coextRestrFun_comp α F r.g₂ I₂.f, r.w]⟩

private theorem coextUnderlyingCompatible
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {𝒪₁ 𝒪₂ : CategoryTheory.Sheaf J RingCat.{u}}
    (α : 𝒪₁ ⟶ 𝒪₂) (F : SheafOfModules.{u} 𝒪₁) {U : C}
    (S : (J).Cover U)
    (φ : ∀ I : S.Arrow, Stacks.PresheafOfModules.CoextendScalars.coextSec α.hom F.val (Opposite.op
      I.Y))
    (hφ : coextCompatible α F S φ) :
    Presieve.FamilyOfElements.Compatible
      (fun V f hf => coextUnderlying α F V (φ ⟨V, f, hf⟩) :
        Presieve.FamilyOfElements (coextPresheafHom α F) (S : Sieve U).arrows) := by
  intro V₁ V₂ W g₁ g₂ f₁ f₂ hf₁ hf₂ hcomm
  rw [coextUnderlying_restr, coextUnderlying_restr]
  exact congrArg (coextUnderlying α F W)
    (hφ (I₁ := ⟨V₁, f₁, hf₁⟩) (I₂ := ⟨V₂, f₂, hf₂⟩)
      (GrothendieckTopology.Cover.Arrow.Relation.mk W g₁ g₂ hcomm))

/-- The presheaf of abelian groups `coextPresheafHom α F` is a sheaf. -/
private theorem coextPresheafHom_isSheaf
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {𝒪₁ 𝒪₂ : CategoryTheory.Sheaf J RingCat.{u}}
    (α : 𝒪₁ ⟶ 𝒪₂) (F : SheafOfModules.{u} 𝒪₁) :
    Presheaf.IsSheaf J (coextPresheafHom α F) :=
  Presheaf.IsSheaf.hom (Stacks.PresheafOfModules.CoextendScalars.O'asOModule α.hom).presheaf
    F.val.presheaf F.isSheaf

private noncomputable def coextGluedUnderlying
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {𝒪₁ 𝒪₂ : CategoryTheory.Sheaf J RingCat.{u}}
    (α : 𝒪₁ ⟶ 𝒪₂) (F : SheafOfModules.{u} 𝒪₁) {U : C}
    (S : (J).Cover U)
    (φ : ∀ I : S.Arrow, Stacks.PresheafOfModules.CoextendScalars.coextSec α.hom F.val (Opposite.op
      I.Y))
    (hφ : coextCompatible α F S φ) : (coextPresheafHom α F).obj (Opposite.op U) :=
  let fam : Presieve.FamilyOfElements (coextPresheafHom α F) (S : Sieve U).arrows :=
    fun V f hf => coextUnderlying α F V (φ ⟨V, f, hf⟩)
  ((coextPresheafHom_isSheaf α F).isSheafFor _ S.2).amalgamate fam
    (coextUnderlyingCompatible α F S φ hφ)

private theorem coextGluedUnderlying_restr
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {𝒪₁ 𝒪₂ : CategoryTheory.Sheaf J RingCat.{u}}
    (α : 𝒪₁ ⟶ 𝒪₂) (F : SheafOfModules.{u} 𝒪₁) {U : C}
    (S : (J).Cover U)
    (φ : ∀ I : S.Arrow, Stacks.PresheafOfModules.CoextendScalars.coextSec α.hom F.val (Opposite.op
      I.Y))
    (hφ : coextCompatible α F S φ) (I : S.Arrow) :
    (coextPresheafHom α F).map I.f.op (coextGluedUnderlying α F S φ hφ) =
      coextUnderlying α F I.Y (φ I) := by
  exact ((coextPresheafHom_isSheaf α F).isSheafFor _ S.2).valid_glue (x := fun V f hf =>
    coextUnderlying α F V (φ ⟨V, f, hf⟩)) (coextUnderlyingCompatible α F S φ hφ) I.f I.hf

private noncomputable def coextGluedHom
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {𝒪₁ 𝒪₂ : CategoryTheory.Sheaf J RingCat.{u}}
    (α : 𝒪₁ ⟶ 𝒪₂) (F : SheafOfModules.{u} 𝒪₁) {U : C}
    (S : (J).Cover U)
    (φ : ∀ I : S.Arrow, Stacks.PresheafOfModules.CoextendScalars.coextSec α.hom F.val (Opposite.op
      I.Y))
    (hφ : coextCompatible α F S φ) :
    Stacks.PresheafOfModules.CoextendScalars.restrictToOver U
      (Stacks.PresheafOfModules.CoextendScalars.O'asOModule α.hom) ⟶
      Stacks.PresheafOfModules.CoextendScalars.restrictToOver U F.val :=
  PresheafOfModules.homMk (coextGluedUnderlying α F S φ hφ) (by
    intro W r m
    let ψ : (Stacks.PresheafOfModules.CoextendScalars.restrictToOver U
      (Stacks.PresheafOfModules.CoextendScalars.O'asOModule α.hom)).presheaf ⟶
        (Stacks.PresheafOfModules.CoextendScalars.restrictToOver U F.val).presheaf :=
          coextGluedUnderlying α F S φ hφ
    have hFslice : Presheaf.IsSheaf ((J).over U)
        (((Stacks.PresheafOfModules.CoextendScalars.restrictToOver U F.val).presheaf)) :=
      (Over.forget U).op_comp_isSheaf_of_isSheaf
        ((J).over U) (J)
        F.val.presheaf F.isSheaf
    obtain ⟨W₀⟩ := W
    let T : ((J).over U).Cover W₀ :=
      ⟨(Sieve.overEquiv W₀).symm ((S : Sieve U).pullback W₀.hom), by
        rw [GrothendieckTopology.mem_over_iff, OrderIso.apply_symm_apply]
        exact (J).pullback_stable W₀.hom S.2⟩
    refine hFslice.isSeparated W₀ T.1 T.2 _ _ ?_
    intro Z g hg
    have hZmem : (S : Sieve U).arrows Z.hom := by
      have hmem : ((Sieve.overEquiv W₀).symm
          ((S : Sieve U).pullback W₀.hom)).arrows g := hg
      rwa [Sieve.overEquiv_symm_iff, Sieve.pullback_apply, Over.w g] at hmem
    have hNsmul : ConcreteCategory.hom ((Stacks.PresheafOfModules.CoextendScalars.restrictToOver U
          (Stacks.PresheafOfModules.CoextendScalars.O'asOModule α.hom)).presheaf.map g.op) (r • m) =
        ConcreteCategory.hom (((Over.forget U).op ⋙ 𝒪₁.obj).map g.op) r •
          ConcreteCategory.hom ((Stacks.PresheafOfModules.CoextendScalars.restrictToOver U
            (Stacks.PresheafOfModules.CoextendScalars.O'asOModule α.hom)).presheaf.map g.op) m :=
      (Stacks.PresheafOfModules.CoextendScalars.restrictToOver U
        (Stacks.PresheafOfModules.CoextendScalars.O'asOModule α.hom)).map_smul g.op r m
    rw [presheaf_map_smul (Stacks.PresheafOfModules.CoextendScalars.restrictToOver U F.val) g.op r
          (ConcreteCategory.hom (ψ.app (Opposite.op W₀)) m),
        ← NatTrans.naturality_apply ψ g.op (r • m),
        ← NatTrans.naturality_apply ψ g.op m, hNsmul]
    let I : S.Arrow := ⟨Z.left, Z.hom, hZmem⟩
    have hrestr := coextGluedUnderlying_restr α F S φ hφ I
    have hmapapp := presheafHom_map_app (F := (Stacks.PresheafOfModules.CoextendScalars.O'asOModule
      α.hom).presheaf)
      (G := F.val.presheaf) (𝟙 Z.left) I.f Z.hom (Category.id_comp Z.hom) ψ
    have hkey : ψ.app (Opposite.op (Over.mk Z.hom)) =
        (coextUnderlying α F I.Y (φ I)).app (Opposite.op (Over.mk (𝟙 Z.left))) := by
      rw [← hmapapp, hrestr]
    have hkeyZ : ψ.app (Opposite.op Z) =
        (coextUnderlying α F I.Y (φ I)).app (Opposite.op (Over.mk (𝟙 Z.left))) := hkey
    rw [hkeyZ]
    exact ((φ I).app (Opposite.op (Over.mk (𝟙 Z.left)))).hom.map_smul _ _)

private theorem coextRestr_gGlued
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {𝒪₁ 𝒪₂ : CategoryTheory.Sheaf J RingCat.{u}}
    (α : 𝒪₁ ⟶ 𝒪₂) (F : SheafOfModules.{u} 𝒪₁) {U : C}
    (S : (J).Cover U)
    (φ : ∀ I : S.Arrow, Stacks.PresheafOfModules.CoextendScalars.coextSec α.hom F.val (Opposite.op
      I.Y))
    (hφ : coextCompatible α F S φ) (I : S.Arrow) :
    Stacks.PresheafOfModules.CoextendScalars.coextRestrFun α.hom F.val I.f.op (coextGluedHom α F S φ
      hφ) = φ I := by
  apply (PresheafOfModules.toPresheaf ((Over.forget I.Y).op ⋙ 𝒪₁.obj)).map_injective
  show coextUnderlying α F I.Y
      (Stacks.PresheafOfModules.CoextendScalars.coextRestrFun α.hom F.val I.f.op (coextGluedHom α F
        S φ hφ)) =
    coextUnderlying α F I.Y (φ I)
  rw [← coextUnderlying_restr]
  exact coextGluedUnderlying_restr α F S φ hφ I

private theorem coextRestrictToCover_bijective
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {𝒪₁ 𝒪₂ : CategoryTheory.Sheaf J RingCat.{u}}
    (α : 𝒪₁ ⟶ 𝒪₂) (F : SheafOfModules.{u} 𝒪₁) {U : C}
    (S : (J).Cover U) :
    Function.Bijective (coextRestrictToCover α F S) := by
  constructor
  · intro ψ ψ' hψ
    apply (PresheafOfModules.toPresheaf ((Over.forget U).op ⋙ 𝒪₁.obj)).map_injective
    apply ((coextPresheafHom_isSheaf α F).isSheafFor S.1 S.2).isSeparatedFor.ext
    intro V f hf
    have hloc := congrFun (congrArg Subtype.val hψ) ⟨V, f, hf⟩
    show (coextPresheafHom α F).map f.op (coextUnderlying α F U ψ) =
      (coextPresheafHom α F).map f.op (coextUnderlying α F U ψ')
    rw [coextUnderlying_restr α F f ψ, coextUnderlying_restr α F f ψ']
    exact congrArg (coextUnderlying α F V) hloc
  · rintro ⟨φ, hφ⟩
    exact ⟨coextGluedHom α F S φ hφ, Subtype.ext (funext (coextRestr_gGlued α F S φ hφ))⟩

private theorem coextObj_isSheaf
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {𝒪₁ 𝒪₂ : CategoryTheory.Sheaf J RingCat.{u}}
    (α : 𝒪₁ ⟶ 𝒪₂) (F : SheafOfModules.{u} 𝒪₁) :
    Presheaf.IsSheaf (J)
      (Stacks.PresheafOfModules.CoextendScalars.coextObj α.hom F.val).presheaf := by
  rw [Presheaf.isSheaf_iff_multifork]
  intro U S
  have hbij := coextRestrictToCover_bijective α F S
  have hι : ∀ I : S.Arrow,
      (S.multifork (Stacks.PresheafOfModules.CoextendScalars.coextObj α.hom F.val).presheaf).ι I =
        (Stacks.PresheafOfModules.CoextendScalars.coextObj α.hom F.val).presheaf.map I.f.op :=
    fun _ => rfl
  set glueEquiv := Equiv.ofBijective (coextRestrictToCover α F S) hbij with hge
  have hsymm : ∀ (φ : ∀ I : S.Arrow,
      Stacks.PresheafOfModules.CoextendScalars.coextSec α.hom F.val (Opposite.op I.Y))
      (h : coextCompatible α F S φ) (I : S.Arrow),
      Stacks.PresheafOfModules.CoextendScalars.coextRestrFun α.hom F.val I.f.op (glueEquiv.symm ⟨φ,
        h⟩) = φ I := by
    intro φ h I
    have heq := glueEquiv.apply_symm_apply ⟨φ, h⟩
    rw [hge, Equiv.ofBijective_apply, coextRestrictToCover] at heq
    exact congrFun (congrArg Subtype.val heq) I
  have hcompat : ∀ (E : Limits.Multifork (S.index (Stacks.PresheafOfModules.CoextendScalars.coextObj
    α.hom F.val).presheaf))
      (e : E.pt),
      coextCompatible α F S (fun I => (ConcreteCategory.hom (E.ι I)) e) := by
    intro E e I₁ I₂ r
    have hcond := E.condition (GrothendieckTopology.Cover.Relation.mk (S := S) r)
    exact ConcreteCategory.congr_hom hcond e
  set L : ∀ (E : Limits.Multifork (S.index (Stacks.PresheafOfModules.CoextendScalars.coextObj α.hom
    F.val).presheaf)),
      E.pt → (Stacks.PresheafOfModules.CoextendScalars.coextObj α.hom F.val).presheaf.obj
        (Opposite.op U) :=
    fun E e => glueEquiv.symm ⟨fun I => (ConcreteCategory.hom (E.ι I)) e,
      hcompat E e⟩ with hL
  have hLrestr : ∀ (E : Limits.Multifork (S.index (Stacks.PresheafOfModules.CoextendScalars.coextObj
    α.hom F.val).presheaf))
      (e : E.pt) (I : S.Arrow),
      Stacks.PresheafOfModules.CoextendScalars.coextRestrFun α.hom F.val I.f.op (L E e) =
        (ConcreteCategory.hom (E.ι I)) e :=
    fun E e I => hsymm _ (hcompat E e) I
  have hadd : ∀ (I : S.Arrow)
      (x y : (Stacks.PresheafOfModules.CoextendScalars.coextObj α.hom F.val).presheaf.obj
        (Opposite.op U)),
      Stacks.PresheafOfModules.CoextendScalars.coextRestrFun α.hom F.val I.f.op (x + y) =
        Stacks.PresheafOfModules.CoextendScalars.coextRestrFun α.hom F.val I.f.op x +
          Stacks.PresheafOfModules.CoextendScalars.coextRestrFun α.hom F.val I.f.op y :=
    fun I x y => Stacks.PresheafOfModules.CoextendScalars.coextRestrFun_add α.hom F.val I.f.op x y
  have hext : ∀ x y : (Stacks.PresheafOfModules.CoextendScalars.coextObj α.hom F.val).presheaf.obj
      (Opposite.op U), (∀ I : S.Arrow,
        Stacks.PresheafOfModules.CoextendScalars.coextRestrFun α.hom F.val I.f.op x =
          Stacks.PresheafOfModules.CoextendScalars.coextRestrFun α.hom F.val I.f.op y) → x = y :=
    fun _ _ h => hbij.injective (Subtype.ext (funext h))
  have hz : ∀ I : S.Arrow,
      Stacks.PresheafOfModules.CoextendScalars.coextRestrFun α.hom F.val I.f.op
        (0 : (Stacks.PresheafOfModules.CoextendScalars.coextObj α.hom F.val).presheaf.obj
          (Opposite.op U)) = 0 := by
    intro I
    have h := hadd I 0 0
    rw [add_zero] at h
    exact left_eq_add.mp h
  refine ⟨Limits.Multifork.IsLimit.mk _ (fun E => ?_) (fun E i => ?_) (fun E m hm => ?_)⟩
  · refine AddCommGrpCat.ofHom
      { toFun := L E
        map_zero' := ?_
        map_add' := ?_ }
    · refine hext _ _ fun I => ?_
      rw [hLrestr, map_zero]
      exact (hz I).symm
    · intro a b
      refine hext _ _ fun I => ?_
      rw [hLrestr, map_add, ← hLrestr E a I, ← hLrestr E b I]
      exact (hadd I _ _).symm
  · apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro e
    show (ConcreteCategory.hom
        ((S.multifork (Stacks.PresheafOfModules.CoextendScalars.coextObj α.hom F.val).presheaf).ι
          i)) (L E e) =
      (ConcreteCategory.hom (E.ι i)) e
    rw [hι i]
    exact hLrestr E e i
  · apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro e
    show (ConcreteCategory.hom m) e = L E e
    refine hext _ _ fun I => ?_
    rw [hLrestr]
    have h2 := ConcreteCategory.congr_hom (hm I) e
    rwa [ConcreteCategory.comp_apply, hι I] at h2

/-- The internal-Hom sheaf `SheafHom_{𝒪₁}(𝒪₂, F)`, whose sections over `U` are the morphisms
`𝒪₂|_U ⟶ F|_U` of `𝒪₁|_U`-modules on the slice `Over U`. -/
noncomputable def homSheafObj
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {𝒪₁ 𝒪₂ : CategoryTheory.Sheaf J RingCat.{u}}
    (α : 𝒪₁ ⟶ 𝒪₂) (F : SheafOfModules.{u} 𝒪₁) : SheafOfModules.{u} 𝒪₂ where
  val := Stacks.PresheafOfModules.CoextendScalars.coextObj α.hom F.val
  isSheaf := by
    exact coextObj_isSheaf α F

/-- The underlying presheaf of the internal-Hom sheaf is the slice-wise internal-Hom presheaf. -/
@[simp]
theorem homSheafObj_val
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {𝒪₁ 𝒪₂ : CategoryTheory.Sheaf J RingCat.{u}}
    (α : 𝒪₁ ⟶ 𝒪₂) (F : SheafOfModules.{u} 𝒪₁) :
    (homSheafObj α F).val = Stacks.PresheafOfModules.CoextendScalars.coextObj α.hom F.val := rfl

/-- Sections of the internal-Hom sheaf over `U` are morphisms on the slice over `U`, with their
natural `𝒪₂(U)`-module structure. -/
@[simp]
theorem homSheafObj_obj
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {𝒪₁ 𝒪₂ : CategoryTheory.Sheaf J RingCat.{u}}
    (α : 𝒪₁ ⟶ 𝒪₂) (F : SheafOfModules.{u} 𝒪₁) (U : Cᵒᵖ) :
    (homSheafObj α F).val.obj U = Stacks.PresheafOfModules.CoextendScalars.coextObjModule α.hom
      F.val U := rfl

/-- The functor `SheafHom_{𝒪₁}(𝒪₂, -)` from `𝒪₁`-modules to `𝒪₂`-modules. On underlying
presheaves it is the coextension of scalars `Stacks.PresheafOfModules.CoextendScalars.coextFunMap`.
-/
@[stacks 0A6F "the internal Hom sheaf, as a functor to modules over the target ring"]
noncomputable def homSheaf
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {𝒪₁ 𝒪₂ : CategoryTheory.Sheaf J RingCat.{u}}
    (α : 𝒪₁ ⟶ 𝒪₂) : SheafOfModules.{u} 𝒪₁ ⥤ SheafOfModules.{u} 𝒪₂ where
  obj F := homSheafObj α F
  map f := ⟨Stacks.PresheafOfModules.CoextendScalars.coextFunMap α.hom f.val⟩
  map_id F :=
    SheafOfModules.hom_ext (Stacks.PresheafOfModules.CoextendScalars.coextFunMap_id α.hom F.val)
  map_comp f g := SheafOfModules.hom_ext
    (Stacks.PresheafOfModules.CoextendScalars.coextFunMap_comp α.hom f.val g.val)

/-- Restriction of scalars along a homomorphism of sheaves of rings is left adjoint to the
internal-Hom functor `SheafHom_{𝒪₁}(𝒪₂, -)`. -/
@[stacks 0A6F "the bifunctorial Hom identification", sga "4 IV 14.5" "adjunction i_* ⊣ i^!"]
noncomputable def restrictScalarsHomAdjunction
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {𝒪₁ 𝒪₂ : CategoryTheory.Sheaf J RingCat.{u}}
    (α : 𝒪₁ ⟶ 𝒪₂) :
    SheafOfModules.restrictScalars.{u} α ⊣ homSheaf α :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun G F =>
        { toFun := fun f => ⟨(Stacks.PresheafOfModules.CoextendScalars.homEquiv α.hom G.val F.val)
          f.val⟩
          invFun := fun f => ⟨(Stacks.PresheafOfModules.CoextendScalars.homEquiv α.hom G.val
            F.val).symm f.val⟩
          left_inv := fun f => SheafOfModules.hom_ext
            ((Stacks.PresheafOfModules.CoextendScalars.homEquiv α.hom G.val F.val).left_inv f.val)
          right_inv := fun f => SheafOfModules.hom_ext
            ((Stacks.PresheafOfModules.CoextendScalars.homEquiv α.hom G.val F.val).right_inv
              f.val) }
      homEquiv_naturality_left_symm := by
        intro G G' γ F β
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.Hom.ext
        ext X g
        change Stacks.PresheafOfModules.CoextendScalars.invSecVal α.hom γ.val X ((F.val ≫ β.val).app
          X g) =
          Stacks.PresheafOfModules.CoextendScalars.invSecVal α.hom γ.val X ((β.val.app X)
            ((F.val.app X) g))
        rw [PresheafOfModules.comp_app]
        rfl
      homEquiv_naturality_right := by
        intro G F F' f η
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.Hom.ext
        ext X g
        change Stacks.PresheafOfModules.CoextendScalars.fwdSec α.hom G.val F'.val (f.val ≫ η.val) X
          g =
          Stacks.PresheafOfModules.CoextendScalars.fwdSec α.hom G.val F.val f.val X g ≫
            (PresheafOfModules.pushforward₀ (Over.forget X.unop) 𝒪₁.obj).map η.val
        ext V a'
        simp only [Stacks.PresheafOfModules.CoextendScalars.fwdSec,
          Stacks.PresheafOfModules.CoextendScalars.fwdSecPresheaf,
            Stacks.PresheafOfModules.CoextendScalars.fwdSecApp,
          PresheafOfModules.comp_app, PresheafOfModules.homMk_app, AddCommGrpCat.ofHom]
        rfl }

end RingedSpaceModuleAdjunction

end
