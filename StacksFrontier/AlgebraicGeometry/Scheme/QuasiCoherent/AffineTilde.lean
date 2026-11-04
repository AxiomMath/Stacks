module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# Associated sheaves and pullback and pushforward along a map of affine schemes

Let `φ : R ⟶ S` be a ring homomorphism and let `Spec φ : Spec S ⟶ Spec R` be the induced
morphism of affine schemes. Pulling the sheaf `M̃` associated to an `R`-module `M` back along
`Spec φ` gives the sheaf associated to the extension of scalars `S ⊗_R M`, naturally in `M`;
pushing the sheaf `Ñ` associated to an `S`-module `N` forward along `Spec φ` gives the sheaf
associated to the restriction of scalars of `N` along `φ`, naturally in `N`.

Each isomorphism comes with the normalization that identifies it as *the* canonical one: on global
sections the pullback comparison sends the pullback of the section represented by `m` to the
section represented by `1 ⊗ m`, and the pushforward comparison sends the section represented by
`n` to the section represented by the same `n`.

## Main definitions

* `AlgebraicGeometry.pushforwardΓLinearEquiv`: the underlying linear equivalence on global
  sections.
* `AlgebraicGeometry.pushforwardΓIso`: pushforward restricts the scalar action on global sections.
* `AlgebraicGeometry.pullbackTildeIso`: pullback of associated sheaves is extension of scalars.
* `AlgebraicGeometry.pushforwardTildeΓIso`: the global sections of a pushed-forward associated
  sheaf are the restriction of scalars of the module.
* `AlgebraicGeometry.pushforwardTildeNatTrans`: the canonical comparison underlying the
  pushforward statement, before it is known to be invertible.
* `AlgebraicGeometry.pushforwardTildeIso`: pushforward of associated sheaves is restriction of
  scalars.

## Main results

* `AlgebraicGeometry.pullbackTildeIso_hom_app_unit_toOpen` normalizes the pullback isomorphism on
  global sections, the first map being the pullback--pushforward adjunction unit.
* `AlgebraicGeometry.pushforwardTildeNatTrans_app_toOpen` and
  `AlgebraicGeometry.pushforwardTildeIso_hom_app_toOpen` normalize the pushforward isomorphism on
  global sections, in each direction.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/
@[expose] public noncomputable section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction
open scoped ChangeOfRings

universe u

/-- The global sections of a pushforward along `Spec φ` are the global sections of the module
itself, with the scalars restricted along `φ`; the underlying map is the identity. -/
public noncomputable def pushforwardΓLinearEquiv
    (R S : CommRingCat.{u}) (φ : R ⟶ S) (N : (Spec S).Modules) :
    ((moduleSpecΓFunctor (R := R)).obj
        ((Scheme.Modules.pushforward (Spec.map φ)).obj N)) ≃ₗ[R]
      ((ModuleCat.restrictScalars φ.hom).obj ((moduleSpecΓFunctor (R := S)).obj N)) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change @SMul.smul Γ(Spec S, ⊤) Γ(N, ⊤) _
      ((Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r)) x =
      @SMul.smul Γ(Spec S, ⊤) Γ(N, ⊤) _ ((Scheme.ΓSpecIso S).inv (φ r)) x
    congr 1
    exact congr($(Scheme.ΓSpecIso_inv_naturality φ) r).symm

/-- Pushforward along a morphism of affine schemes restricts the scalar action on global
sections; the underlying map of this comparison is the identity. -/
public noncomputable def pushforwardΓIso (R S : CommRingCat.{u}) (φ : R ⟶ S) :
    Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor ≅
      moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom :=
  NatIso.ofComponents (fun N ↦ LinearEquiv.toModuleIso (pushforwardΓLinearEquiv R S φ N))
    (fun h ↦ by ext x; rfl)

/-- Pullback along the map of affine schemes induced by `f : R ⟶ S` carries the associated sheaf
of an `R`-module to the associated sheaf of its extension of scalars to `S`, naturally in the
module. -/
@[stacks 01I9 "affine_pullback_tilde"]
public noncomputable def pullbackTildeIso (R S : CommRingCat.{u}) (f : R ⟶ S) :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map f) ≅
      ModuleCat.extendScalars f.hom ⋙ tilde.functor S :=
  ((tilde.adjunction.comp
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f))).ofNatIsoRight
      (pushforwardΓIso R S f)).leftAdjointUniq
    ((ModuleCat.extendRestrictScalarsAdj f.hom).comp tilde.adjunction)

/-- The canonical affine pullback comparison sends the pullback of the global
section represented by `m` to the global section represented by `1 ⊗ m`.
Here the first map is the pullback--pushforward adjunction unit. -/
@[stacks 01I9 "affine_pullback_tilde"]
public theorem pullbackTildeIso_hom_app_unit_toOpen
    (R S : CommRingCat.{u}) (f : R ⟶ S) (M : ModuleCat R) (m : M) :
    ((pullbackTildeIso R S f).hom.app M).val.app (.op ⊤)
      (((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).unit.app
        (tilde M)).val.app (.op ⊤) (tilde.toOpen M ⊤ m)) =
    tilde.toOpen ((ModuleCat.extendScalars f.hom).obj M) ⊤
      ((1 : S) ⊗ₜ[R, f.hom] m) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((tilde.adjunction.comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f))).ofNatIsoRight
        (pushforwardΓIso R S f))
    ((ModuleCat.extendRestrictScalarsAdj f.hom).comp tilde.adjunction) M
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Adjunction.comp_unit_app] at h
  exact congr($(h).hom m)

/-- The global sections of the pushforward of an associated sheaf: for an `S`-module `N`, the
`R`-module of global sections of `Spec φ_* Ñ` is `N` with its scalars restricted along `φ`,
naturally in `N`. -/
public noncomputable def pushforwardTildeΓIso (R S : CommRingCat.{u}) (φ : R ⟶ S) :
    ModuleCat.restrictScalars φ.hom ≅
      tilde.functor S ⋙ Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (tilde.toTildeΓNatIso (R := S)) (ModuleCat.restrictScalars φ.hom) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (tilde.functor S) (pushforwardΓIso R S φ).symm

/-- The canonical comparison from the sheaf associated to the restriction of scalars of an
`S`-module to the pushforward along `Spec φ` of the sheaf associated to that module: apply
`tilde` to `pushforwardTildeΓIso` and then the counit `Scheme.Modules.fromTildeΓNatTrans` of
the tilde--global-sections adjunction over `R`. -/
public noncomputable def pushforwardTildeNatTrans (R S : CommRingCat.{u}) (φ : R ⟶ S) :
    ModuleCat.restrictScalars φ.hom ⋙ tilde.functor R ⟶
      tilde.functor S ⋙ Scheme.Modules.pushforward (Spec.map φ) :=
  Functor.whiskerRight (pushforwardTildeΓIso R S φ).hom (tilde.functor R) ≫
    Functor.whiskerLeft (tilde.functor S ⋙ Scheme.Modules.pushforward (Spec.map φ))
      (Scheme.Modules.fromTildeΓNatTrans (R := R))

/-- Every component of `pushforwardTildeNatTrans` is an isomorphism. -/
public instance isIso_pushforwardTildeNatTrans_app (R S : CommRingCat.{u}) (φ : R ⟶ S)
    (N : ModuleCat S) : IsIso ((pushforwardTildeNatTrans R S φ).app N) := by
  dsimp only [pushforwardTildeNatTrans, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  have h : IsIso ((Scheme.Modules.fromTildeΓNatTrans (R := R)).app
      ((tilde.functor S ⋙ Scheme.Modules.pushforward (Spec.map φ)).obj N)) :=
    isIso_fromTildeΓ_pushforward φ (tilde N)
  infer_instance

/-- `pushforwardTildeNatTrans` is an isomorphism of functors. -/
public instance isIso_pushforwardTildeNatTrans (R S : CommRingCat.{u}) (φ : R ⟶ S) :
    IsIso (pushforwardTildeNatTrans R S φ) := NatIso.isIso_of_isIso_app _

/-- Pushforward along the map of affine schemes induced by `φ : R ⟶ S` carries the associated
sheaf of an `S`-module to the associated sheaf of its restriction of scalars along `φ`, naturally
in the module. -/
@[stacks 01I9 "affine_pushforward_tilde"]
public noncomputable def pushforwardTildeIso (R S : CommRingCat.{u}) (φ : R ⟶ S) :
    tilde.functor S ⋙ Scheme.Modules.pushforward (Spec.map φ) ≅
      ModuleCat.restrictScalars φ.hom ⋙ tilde.functor R :=
  (asIso (pushforwardTildeNatTrans R S φ)).symm

/-- The comparison `pushforwardTildeNatTrans` is normalized by the canonical maps from the
underlying modules: on global sections it sends the section of the associated sheaf of the
restricted `R`-module represented by `n` to the section of the associated sheaf of `N`
represented by the same `n`. -/
public theorem pushforwardTildeNatTrans_app_toOpen
    (R S : CommRingCat.{u}) (φ : R ⟶ S) (N : ModuleCat S) (n : N) :
    ((pushforwardTildeNatTrans R S φ).app N).val.app (Opposite.op (⊤ : (Spec R).Opens))
      (tilde.toOpen ((ModuleCat.restrictScalars φ.hom).obj N) (⊤ : (Spec R).Opens) n) =
    tilde.toOpen N (⊤ : (Spec S).Opens) n := by
  set M := (Scheme.Modules.pushforward (Spec.map φ)).obj (tilde N)
  set η := (pushforwardTildeΓIso R S φ).hom.app N
  change ((modulesSpecToSheaf.map (tilde.map η)).1.app (.op ⊤) ≫
      (modulesSpecToSheaf.map M.fromTildeΓ).1.app (.op ⊤))
    (tilde.toOpen ((ModuleCat.restrictScalars φ.hom).obj N) ⊤ n) = _
  have h₁ : (modulesSpecToSheaf.map (tilde.map η)).1.app (.op ⊤)
      (tilde.toOpen ((ModuleCat.restrictScalars φ.hom).obj N) ⊤ n) =
      tilde.toOpen ((moduleSpecΓFunctor (R := R)).obj M) ⊤ (η n) := by
    exact (congrArg (fun g ↦ g.hom n) (tilde.toOpen_map_app η (⊤ : (Spec R).Opens)) :)
  have h₂ : (modulesSpecToSheaf.map M.fromTildeΓ).1.app (.op ⊤)
      (tilde.toOpen ((moduleSpecΓFunctor (R := R)).obj M) ⊤ (η n)) = η n := by
    have hh := congr($(Scheme.Modules.toOpen_fromTildeΓ_app M (⊤ : (Spec R).Opens)) (η n))
    refine Eq.trans (CategoryTheory.comp_apply _ _ _).symm (hh.trans ?_)
    simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, ModuleCat.hom_id,
      Functor.comp_obj, LinearMap.id_coe]
    rfl
  exact (CategoryTheory.comp_apply _ _ _).trans
    ((congrArg ((modulesSpecToSheaf.map M.fromTildeΓ).1.app (.op ⊤)) h₁).trans h₂)

/-- The canonical affine pushforward comparison is normalized by the canonical identifications of
a module with the global sections of its associated sheaf: its component at `N` sends the global
section represented by `n` on `Spec S` to the global section represented by the same element of
the restricted `R`-module on `Spec R`. -/
@[stacks 01I9 "affine_pushforward_tilde"]
public theorem pushforwardTildeIso_hom_app_toOpen
    (R S : CommRingCat.{u}) (φ : R ⟶ S) (N : ModuleCat S) (n : N) :
    ((pushforwardTildeIso R S φ).hom.app N).val.app (Opposite.op (⊤ : (Spec R).Opens))
      (tilde.toOpen N (⊤ : (Spec S).Opens) n) =
    tilde.toOpen ((ModuleCat.restrictScalars φ.hom).obj N) (⊤ : (Spec R).Opens) n := by
  have hid := congrArg (fun g ↦ g.val.app (Opposite.op (⊤ : (Spec R).Opens)))
    ((pushforwardTildeIso R S φ).inv_hom_id_app N)
  change ((pushforwardTildeIso R S φ).inv.app N).val.app (.op ⊤) ≫
      ((pushforwardTildeIso R S φ).hom.app N).val.app (.op ⊤) = 𝟙 _ at hid
  rw [← pushforwardTildeNatTrans_app_toOpen R S φ N n]
  change (((pushforwardTildeIso R S φ).inv.app N).val.app (.op ⊤) ≫
      ((pushforwardTildeIso R S φ).hom.app N).val.app (.op ⊤))
    (tilde.toOpen ((ModuleCat.restrictScalars φ.hom).obj N) ⊤ n) = _
  rw [hid]
  rfl

end AlgebraicGeometry
