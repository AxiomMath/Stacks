module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianChangeOfRings

/-!
# Transporting a cartesian presheaf of modules along a ring map

Let `M` be a presheaf of modules over a presheaf of commutative rings `R` on a category `C`, let
`f : X ⟶ Y` be a morphism of `Cᵒᵖ` and let `h : R Y ⟶ T` be a ring map.  The restriction map of
`M` along `f` induces the `T`-linear map
`T ⊗_{R X, h ∘ R(f)} M X ⟶ T ⊗_{R Y, h} M Y`, `t ⊗ x ↦ t ⊗ M(f) x`,
which is an isomorphism as soon as `M` is cartesian along `f`: it is the extension of scalars
along `h` of the base-change comparison `R Y ⊗_{R X} M X ⟶ M Y`.  These *transport maps* compose
along composable morphisms and commute with further extension of scalars, and every equation
between composites of them is checked on the generators `1 ⊗ x`.  The degree-zero description of
the cartesian cosimplicial modules and the homotopy invariance of base change on them are built
from these maps.

## Main definitions

* `ModuleCat.extendScalarsSemilinear`: the `g`-semilinear map `S ⊗_{R, f} M ⟶ T ⊗_{R, g ∘ f} M`
  fixing the generators `1 ⊗ x`.
* `Stacks.PresheafOfModules.transport`: the transport map
  `T ⊗_{R X, k} M X ⟶ T ⊗_{R Y, h} M Y` of `f : X ⟶ Y`, for `k = h ∘ R(f)`.

## Main results

* `Stacks.PresheafOfModules.transport_one_tmul`: the transport map sends `1 ⊗ x` to
  `1 ⊗ M(f) x`.
* `Stacks.PresheafOfModules.transport_comp`: transport maps compose along composable morphisms.
* `Stacks.PresheafOfModules.isIso_transport`: the transport map of a morphism along which `M` is
  cartesian is an isomorphism.
* `Stacks.PresheafOfModules.transport_comp_extendScalarsSemilinear`: transport maps commute with
  further extension of scalars.
* `Stacks.PresheafOfModules.ChangeOfRings.changeOfRings_map_eq`: the restriction maps of a change
  of rings `O₂ ⊗_{O₁} M` are a semilinear extension of scalars followed by a transport map of `M`.
* `Stacks.PresheafOfModules.eq_of_isIso_restrictionBaseChange`: two semilinear maps out of `M Y`
  agree as soon as they agree on the image of `M X`, when `M` is cartesian along `f : X ⟶ Y`.

## References

* [Stacks Project, Tag 039Y](https://stacks.math.columbia.edu/tag/039Y)
-/

@[expose] public section

open CategoryTheory TensorProduct
open scoped ChangeOfRings

universe u v r m

namespace ModuleCat

variable {R S T : Type r} [CommRing R] [CommRing S] [CommRing T]

/-- The `g`-semilinear map `S ⊗_{R, f} M ⟶ T ⊗_{R, gf} M` fixing the generators `1 ⊗ x`, for a
ring map `gf` equal to `g ∘ f`. -/
noncomputable def extendScalarsSemilinear (f : R →+* S) (g : S →+* T) (gf : R →+* T)
    (h : gf = g.comp f) (M : ModuleCat.{max m r} R) :
    (extendScalars f).obj M ⟶ (restrictScalars g).obj ((extendScalars gf).obj M) :=
  ((extendRestrictScalarsAdj f).homEquiv _ _).symm
    ((extendRestrictScalarsAdj gf).unit.app M ≫ (restrictScalarsComp' f g gf h).hom.app _)

/-- `extendScalarsSemilinear f g gf h M` sends the generator `1 ⊗ x` of `S ⊗_{R, f} M` to the
generator `1 ⊗ x` of `T ⊗_{R, gf} M`. -/
theorem extendScalarsSemilinear_one_tmul (f : R →+* S) (g : S →+* T) (gf : R →+* T)
    (h : gf = g.comp f) (M : ModuleCat.{max m r} R) (x : M) :
    extendScalarsSemilinear f g gf h M ((1 : S) ⊗ₜ[R, f] x) = (1 : T) ⊗ₜ[R, gf] x :=
  congrArg (fun a => a x) (((extendRestrictScalarsAdj f).homEquiv M
    ((restrictScalars g).obj ((extendScalars gf).obj M))).apply_symm_apply
      ((extendRestrictScalarsAdj gf).unit.app M ≫ (restrictScalarsComp' f g gf h).hom.app _))

end ModuleCat

namespace Stacks.PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{r}}
  (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))

/-- **The transport map of a restriction map.**  For `f : X ⟶ Y` in `Cᵒᵖ`, a ring map
`h : R Y ⟶ T` and `k = h ∘ R(f)`, the `T`-linear map `T ⊗_{R X, k} M X ⟶ T ⊗_{R Y, h} M Y`
sending `t ⊗ x` to `t ⊗ M(f) x`. -/
noncomputable def transport {X Y : Cᵒᵖ} (f : X ⟶ Y) {T : Type r} [CommRing T]
    (h : R.obj Y →+* T) (k : R.obj X →+* T) (hk : k = h.comp (R.map f).hom) :
    (ModuleCat.extendScalars k).obj (M.obj X) ⟶ (ModuleCat.extendScalars h).obj (M.obj Y) :=
  ((ModuleCat.extendRestrictScalarsAdj k).homEquiv _ _).symm
    (M.map f ≫ (ModuleCat.restrictScalars (R.map f).hom).map
      ((ModuleCat.extendRestrictScalarsAdj h).unit.app (M.obj Y)) ≫
      (ModuleCat.restrictScalarsComp' (R.map f).hom h k hk).inv.app _)

/-- The transport map sends `1 ⊗ x` to `1 ⊗ M(f) x`. -/
theorem transport_one_tmul {X Y : Cᵒᵖ} (f : X ⟶ Y) {T : Type r} [CommRing T]
    (h : R.obj Y →+* T) (k : R.obj X →+* T) (hk : k = h.comp (R.map f).hom) (x : M.obj X) :
    transport M f h k hk ((1 : T) ⊗ₜ[R.obj X, k] x) = (1 : T) ⊗ₜ[R.obj Y, h] (M.map f x) :=
  congrArg (fun a => a x) (((ModuleCat.extendRestrictScalarsAdj k).homEquiv (M.obj X)
    ((ModuleCat.extendScalars h).obj (M.obj Y))).apply_symm_apply
      (M.map f ≫ (ModuleCat.restrictScalars (R.map f).hom).map
        ((ModuleCat.extendRestrictScalarsAdj h).unit.app (M.obj Y)) ≫
        (ModuleCat.restrictScalarsComp' (R.map f).hom h k hk).inv.app _))

/-- **Transport maps compose** along composable morphisms. -/
theorem transport_comp {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) {T : Type r} [CommRing T]
    (h : R.obj Z →+* T) (k' : R.obj Y →+* T) (k : R.obj X →+* T)
    (hk' : k' = h.comp (R.map g).hom) (hk : k = k'.comp (R.map f).hom)
    (hk'' : k = h.comp (R.map (f ≫ g)).hom) :
    transport M f k' k hk ≫ transport M g h k' hk' = transport M (f ≫ g) h k hk'' :=
  ModuleCat.ExtendScalars.hom_ext fun x =>
    (congrArg (transport M g h k' hk') (transport_one_tmul M f k' k hk x)).trans
      ((transport_one_tmul M g h k' hk' _).trans
        ((congrArg (fun y : M.obj Z => (1 : T) ⊗ₜ[R.obj Z, h] y)
          (M.map_comp_apply f g x).symm).trans
          (transport_one_tmul M (f ≫ g) h k hk'' x).symm))

/-- Transport maps along equal morphisms agree. -/
theorem transport_congr {X Y : Cᵒᵖ} {f f' : X ⟶ Y} (hf : f = f') {T : Type r} [CommRing T]
    (h : R.obj Y →+* T) (k : R.obj X →+* T) (hk : k = h.comp (R.map f).hom)
    (hk' : k = h.comp (R.map f').hom) : transport M f h k hk = transport M f' h k hk' := by
  subst hf
  rfl

/-- `Stacks.PresheafOfModules.transport_comp`, the composite transport map being reindexed along
a morphism equal to the composite. -/
theorem transport_comp_of_eq {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : f ≫ g = fg) {T : Type r} [CommRing T]
    (h : R.obj Z →+* T) (k' : R.obj Y →+* T) (k : R.obj X →+* T)
    (hk' : k' = h.comp (R.map g).hom) (hk : k = k'.comp (R.map f).hom)
    (hk'' : k = h.comp (R.map fg).hom) :
    transport M f k' k hk ≫ transport M g h k' hk' = transport M fg h k hk'' := by
  subst hfg
  exact transport_comp M f g h k' k hk' hk hk''

/-- The inverse of a transport map, through a composite. -/
theorem inv_transport_eq_of_comp {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : f ≫ g = fg) {T : Type r} [CommRing T]
    (h : R.obj Z →+* T) (k' : R.obj Y →+* T) (k : R.obj X →+* T)
    (hk' : k' = h.comp (R.map g).hom) (hk : k = k'.comp (R.map f).hom)
    (hk'' : k = h.comp (R.map fg).hom)
    [IsIso (transport M g h k' hk')] [IsIso (transport M fg h k hk'')] :
    inv (transport M g h k' hk') = inv (transport M fg h k hk'') ≫ transport M f k' k hk := by
  rw [IsIso.eq_inv_comp, ← transport_comp_of_eq M f g fg hfg h k' k hk' hk hk'',
    Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- A transport map, through a composite. -/
theorem transport_eq_comp_inv {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : f ≫ g = fg) {T : Type r} [CommRing T]
    (h : R.obj Z →+* T) (k' : R.obj Y →+* T) (k : R.obj X →+* T)
    (hk' : k' = h.comp (R.map g).hom) (hk : k = k'.comp (R.map f).hom)
    (hk'' : k = h.comp (R.map fg).hom) [IsIso (transport M g h k' hk')] :
    transport M f k' k hk = transport M fg h k hk'' ≫ inv (transport M g h k' hk') := by
  rw [IsIso.eq_comp_inv, transport_comp_of_eq M f g fg hfg h k' k hk' hk hk'']

/-- The inverse of a transport map, through a composite whose second factor is given. -/
theorem inv_transport_eq_comp_inv {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : f ≫ g = fg) {T : Type r} [CommRing T]
    (h : R.obj Z →+* T) (k' : R.obj Y →+* T) (k : R.obj X →+* T)
    (hk' : k' = h.comp (R.map g).hom) (hk : k = k'.comp (R.map f).hom)
    (hk'' : k = h.comp (R.map fg).hom)
    [IsIso (transport M f k' k hk)] [IsIso (transport M fg h k hk'')] :
    inv (transport M f k' k hk) = transport M g h k' hk' ≫ inv (transport M fg h k hk'') :=
  IsIso.inv_eq_of_hom_inv_id <| by
    rw [← Category.assoc, transport_comp_of_eq M f g fg hfg h k' k hk' hk hk'', IsIso.hom_inv_id]

/-- The inverse of a transport map followed by the transport map of a composite. -/
theorem inv_transport_comp_transport {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : f ≫ g = fg) {T : Type r} [CommRing T]
    (h : R.obj Z →+* T) (k' : R.obj Y →+* T) (k : R.obj X →+* T)
    (hk' : k' = h.comp (R.map g).hom) (hk : k = k'.comp (R.map f).hom)
    (hk'' : k = h.comp (R.map fg).hom) [IsIso (transport M f k' k hk)] :
    inv (transport M f k' k hk) ≫ transport M fg h k hk'' = transport M g h k' hk' := by
  rw [IsIso.inv_comp_eq, transport_comp_of_eq M f g fg hfg h k' k hk' hk hk'']

/-- Composing ring maps out of a presheaf of rings along two successive restriction maps. -/
theorem ringHom_comp_map_comp {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) {T : Type*} [Semiring T]
    (h : R.obj Z →+* T) :
    (h.comp (R.map g).hom).comp (R.map f).hom = h.comp (R.map (f ≫ g)).hom := by
  rw [R.map_comp]
  rfl

/-- The transport map along `k = h ∘ R(f)` taken on the nose is the extension of scalars along `h`
of the base-change comparison of `M` along `f`. -/
theorem transport_eq_comp {X Y : Cᵒᵖ} (f : X ⟶ Y) {T : Type r} [CommRing T]
    (h : R.obj Y →+* T) :
    transport M f h (h.comp (R.map f).hom) rfl =
      (ModuleCat.extendScalarsComp (R.map f).hom h).hom.app (M.obj X) ≫
        (ModuleCat.extendScalars h).map (restrictionBaseChange M f) :=
  ModuleCat.ExtendScalars.hom_ext fun x =>
    (transport_one_tmul M f h _ rfl x).trans
      (((congrArg (fun y : M.obj Y => (1 : T) ⊗ₜ[R.obj Y, h] y)
          (restrictionBaseChange_one_tmul M f x)).symm.trans
        (ModuleCat.ExtendScalars.map_tmul h (restrictionBaseChange M f) 1 _).symm).trans
        (congrArg ((ModuleCat.extendScalars h).map (restrictionBaseChange M f))
          (ModuleCat.extendScalarsComp_hom_app_one_tmul (R.map f).hom h (M.obj X) x).symm))

/-- **The transport map of a cartesian restriction map is an isomorphism.** -/
instance isIso_transport {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso (restrictionBaseChange M f)]
    {T : Type r} [CommRing T] (h : R.obj Y →+* T) (k : R.obj X →+* T)
    (hk : k = h.comp (R.map f).hom) : IsIso (transport M f h k hk) := by
  subst hk
  rw [transport_eq_comp]
  infer_instance

/-- **Transport maps commute with extension of scalars**: extending scalars along `s : T ⟶ T'`
after transporting along `f` is transporting along `f` after extending scalars. -/
@[reassoc]
theorem transport_comp_extendScalarsSemilinear {X Y : Cᵒᵖ} (f : X ⟶ Y) {T T' : Type r}
    [CommRing T] [CommRing T'] (s : T →+* T') (h : R.obj Y →+* T) (k : R.obj X →+* T)
    (hk : k = h.comp (R.map f).hom) (sh : R.obj Y →+* T') (hsh : sh = s.comp h)
    (sk : R.obj X →+* T') (hsk : sk = s.comp k) (hsk' : sk = sh.comp (R.map f).hom) :
    transport M f h k hk ≫ ModuleCat.extendScalarsSemilinear h s sh hsh (M.obj Y) =
      ModuleCat.extendScalarsSemilinear k s sk hsk (M.obj X) ≫
        (ModuleCat.restrictScalars s).map (transport M f sh sk hsk') :=
  ModuleCat.ExtendScalars.hom_ext fun x =>
    (congrArg (ModuleCat.extendScalarsSemilinear h s sh hsh (M.obj Y))
        (transport_one_tmul M f h k hk x)).trans
      ((ModuleCat.extendScalarsSemilinear_one_tmul h s sh hsh (M.obj Y) _).trans
        ((transport_one_tmul M f sh sk hsk' x).symm.trans
          (congrArg (transport M f sh sk hsk')
            (ModuleCat.extendScalarsSemilinear_one_tmul k s sk hsk (M.obj X) x).symm)))

/-- `Stacks.PresheafOfModules.transport_comp_extendScalarsSemilinear` for the inverses of two
transport maps that are isomorphisms. -/
@[reassoc]
theorem inv_transport_comp_extendScalarsSemilinear {X Y : Cᵒᵖ} (f : X ⟶ Y) {T T' : Type r}
    [CommRing T] [CommRing T'] (s : T →+* T') (h : R.obj Y →+* T) (k : R.obj X →+* T)
    (hk : k = h.comp (R.map f).hom) (sh : R.obj Y →+* T') (hsh : sh = s.comp h)
    (sk : R.obj X →+* T') (hsk : sk = s.comp k) (hsk' : sk = sh.comp (R.map f).hom)
    [IsIso (transport M f h k hk)] [IsIso (transport M f sh sk hsk')] :
    inv (transport M f h k hk) ≫ ModuleCat.extendScalarsSemilinear k s sk hsk (M.obj X) =
      ModuleCat.extendScalarsSemilinear h s sh hsh (M.obj Y) ≫
        (ModuleCat.restrictScalars s).map (inv (transport M f sh sk hsk')) := by
  rw [IsIso.inv_comp_eq, ← Category.assoc, transport_comp_extendScalarsSemilinear M f s h k hk sh
    hsh sk hsk hsk', Category.assoc, ← CategoryTheory.Functor.map_comp, IsIso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- Transport maps are natural in the presheaf of modules. -/
theorem transport_naturality {M M' : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat)}
    (a : M ⟶ M') {X Y : Cᵒᵖ} (f : X ⟶ Y) {T : Type r} [CommRing T]
    (h : R.obj Y →+* T) (k : R.obj X →+* T) (hk : k = h.comp (R.map f).hom) :
    (ModuleCat.extendScalars k).map (a.app X) ≫ transport M' f h k hk =
      transport M f h k hk ≫ (ModuleCat.extendScalars h).map (a.app Y) :=
  ModuleCat.ExtendScalars.hom_ext fun x =>
    (congrArg (transport M' f h k hk) (ModuleCat.ExtendScalars.map_tmul k (a.app X) 1 x)).trans
      ((transport_one_tmul M' f h k hk _).trans
        ((congrArg (fun y : M'.obj Y => (1 : T) ⊗ₜ[R.obj Y, h] y)
            (PresheafOfModules.naturality_apply a f x).symm).trans
          ((ModuleCat.ExtendScalars.map_tmul h (a.app Y) 1 _).symm.trans
            (congrArg ((ModuleCat.extendScalars h).map (a.app Y))
              (transport_one_tmul M f h k hk x).symm))))

/-- Inverse transport maps are natural in the presheaf of modules. -/
theorem inv_transport_naturality
    {M M' : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat)}
    (a : M ⟶ M') {X Y : Cᵒᵖ} (f : X ⟶ Y) {T : Type r} [CommRing T]
    (h : R.obj Y →+* T) (k : R.obj X →+* T) (hk : k = h.comp (R.map f).hom)
    [IsIso (transport M f h k hk)] [IsIso (transport M' f h k hk)] :
    (ModuleCat.extendScalars h).map (a.app Y) ≫ inv (transport M' f h k hk) =
      inv (transport M f h k hk) ≫ (ModuleCat.extendScalars k).map (a.app X) := by
  rw [IsIso.comp_inv_eq, Category.assoc, transport_naturality, IsIso.inv_hom_id_assoc]

/-- **A semilinear map out of `M Y` is determined on the image of `M X`** when `M` is cartesian
along `f : X ⟶ Y`: the image of the restriction map generates `M Y` as an `R Y`-module. -/
theorem eq_of_isIso_restrictionBaseChange {X Y : Cᵒᵖ} (f : X ⟶ Y)
    [IsIso (restrictionBaseChange M f)] {S : Type*} [Ring S] (ψ : R.obj Y →+* S)
    {N : Type*} [AddCommGroup N] [Module S N] (g₁ g₂ : M.obj Y →+ N)
    (h₁ : ∀ (a : R.obj Y) (y : M.obj Y), g₁ (a • y) = ψ a • g₁ y)
    (h₂ : ∀ (a : R.obj Y) (y : M.obj Y), g₂ (a • y) = ψ a • g₂ y)
    (h : ∀ x : M.obj X, g₁ (M.map f x) = g₂ (M.map f x)) : g₁ = g₂ := by
  ext y
  obtain ⟨t, rfl⟩ := (asIso (restrictionBaseChange M f)).toLinearEquiv.surjective y
  change g₁ (restrictionBaseChange M f t) = g₂ (restrictionBaseChange M f t)
  induction t using TensorProduct.induction_on with
  | zero =>
    exact (congrArg g₁ (restrictionBaseChange M f).hom.map_zero).trans
      (g₁.map_zero.trans (g₂.map_zero.symm.trans
        (congrArg g₂ (restrictionBaseChange M f).hom.map_zero).symm))
  | tmul a x =>
    exact (congrArg g₁ (restrictionBaseChange_tmul M f a x)).trans
      ((h₁ a _).trans ((congrArg (ψ a • ·) (h x)).trans
        ((h₂ a _).symm.trans (congrArg g₂ (restrictionBaseChange_tmul M f a x)).symm)))
  | add t t' ht ht' =>
    exact (congrArg g₁ ((restrictionBaseChange M f).hom.map_add t t')).trans
      ((g₁.map_add _ _).trans ((congrArg₂ (· + ·) ht ht').trans
        ((g₂.map_add _ _).symm.trans
          (congrArg g₂ ((restrictionBaseChange M f).hom.map_add t t')).symm)))

namespace ChangeOfRings

variable {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{r}}

/-- **The restriction maps of a change of rings.**  The restriction map of `O₂ ⊗_{O₁} M` along
`f : X ⟶ Y` is the semilinear extension of scalars `O₂ X ⊗ M X ⟶ O₂ Y ⊗ M X` followed by the
transport map of `M` along `f`. -/
theorem changeOfRings_map_eq (θ : O₁ ⟶ O₂)
    (M : PresheafOfModules.{max m r} (ringPresheaf O₁)) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (hk : (O₂.map f).hom.comp (θ.app X).hom = (θ.app Y).hom.comp (O₁.map f).hom) :
    ((changeOfRings θ).obj M).map f =
      ModuleCat.extendScalarsSemilinear (θ.app X).hom (O₂.map f).hom
          ((O₂.map f).hom.comp (θ.app X).hom) rfl (M.obj X) ≫
        (ModuleCat.restrictScalars (O₂.map f).hom).map
          (transport M f (θ.app Y).hom ((O₂.map f).hom.comp (θ.app X).hom) hk) :=
  ModuleCat.ExtendScalars.hom_ext fun x =>
    (cofMap_tmul θ M f 1 x).trans <|
      (congrArg (fun c => c ⊗ₜ[O₁.obj Y, (θ.app Y).hom] (M.map f x)) (map_one _)).trans <|
        (transport_one_tmul M f (θ.app Y).hom _ hk x).symm.trans
          (congrArg (transport M f (θ.app Y).hom _ hk)
            (ModuleCat.extendScalarsSemilinear_one_tmul (θ.app X).hom (O₂.map f).hom _ rfl
              (M.obj X) x).symm)

/-- The components of the change of rings of a morphism are extensions of scalars. -/
theorem changeOfRings_map_app (θ : O₁ ⟶ O₂)
    {M M' : PresheafOfModules.{max m r} (ringPresheaf O₁)} (a : M ⟶ M') (X : Cᵒᵖ) :
    ((changeOfRings θ).map a).app X = (ModuleCat.extendScalars (θ.app X).hom).map (a.app X) :=
  ModuleCat.ExtendScalars.hom_ext fun x =>
    (cofHom_app_tmul θ a X 1 x).trans
      (ModuleCat.ExtendScalars.map_tmul (θ.app X).hom (a.app X) 1 x).symm

end ChangeOfRings

end Stacks.PresheafOfModules

end
