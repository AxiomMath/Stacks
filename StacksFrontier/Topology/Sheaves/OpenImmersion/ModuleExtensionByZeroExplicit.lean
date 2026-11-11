module

public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZeroExact

/-!
# Stacks 00A7 — the explicit extension by zero of (pre)sheaves of modules

Let `(X, 𝒪)` be a ringed space and let `j : (U, 𝒪|_U) → (X, 𝒪)` be an open subspace. Following
Stacks 00A4 (5), the *extension by zero* of a presheaf `F` of `𝒪|_U`-modules is the presheaf of
`𝒪`-modules

* `j_{p!}F(V) = F(V)` if `V ⊆ U`,
* `j_{p!}F(V) = 0` if `V ⊄ U`,

with the restriction maps of `F` between opens contained in `U` and zero restriction maps
otherwise, and the extension by zero of a sheaf `F` of `𝒪|_U`-modules is the sheafification
`j_!F` of `j_{p!}F`. This file builds these functors explicitly and proves Stacks 00A7:

1. `j_{p!}` is left adjoint to restriction `PMod(𝒪) ⥤ PMod(𝒪|_U)`
   (`ExtensionByZeroModules.extendByZeroAdjunction`);
2. `j_!` is left adjoint to restriction `Mod(𝒪) ⥤ Mod(𝒪|_U)`
   (`ExtensionByZeroModules.jShriekExplicitAdjunction`);
3. `(j_!F)_x = 0` for `x ∉ U` and `(j_!F)_x = F_x` for `x ∈ U`, the latter linearly along the
   canonical isomorphism `𝒪_{X,x} ≅ 𝒪|_U,x` of the ring stalks
   (`ExtensionByZeroModules.isZero_stalk_jShriekExplicit`,
   `ExtensionByZeroModules.stalkJShriekExplicitLinearEquiv`);
4. `j^{-1} j_! = id` on sheaves of `𝒪|_U`-modules
   (`ExtensionByZeroModules.jShriekExplicitCompJStarIso`).

## Implementation notes

* The sections of `j_{p!}F` over `V` are written uniformly as the functions
  `PLift (V ≤ U) → F(j⁻¹ V)` (`ExtensionByZeroModules.ExtSec`): this is `F(j⁻¹ V)` when `V ⊆ U`
  and the zero module otherwise, avoiding a case split in the type. For `V ⊆ U` the open `j⁻¹ V`
  of `U` is `V` itself, viewed in `U`.
* The adjunction of (1) is built by hand, as a natural bijection
  `Hom(j_{p!}F, G) ≃ Hom(F, G|_U)`. It identifies the explicit `j_{p!}` with Mathlib's abstract
  left adjoint `PresheafOfModules.pullback` of restriction
  (`ExtensionByZeroModules.extendByZeroIsoJpShriek`), and hence the explicit `j_!` with
  `SheafOfModules.pullback` (`ExtensionByZeroModules.jShriekExplicitIso`), through which (2), (3)
  and (4) are transported from `StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero`
  and `StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZeroExact`.
* The stalks in (3) are the stalks of the underlying abelian sheaves, with Mathlib's module
  structure over the stalk of the ring (`PresheafOfModules.instModuleStalk`); a module vanishes
  exactly when its underlying group does. At `x ∈ U`, written `x = j u` for the point `u` of the
  subspace `U`, the identification `(j_!F)_x ≅ F_x` is semilinear along the identification
  `𝒪_{X,x} ≅ 𝒪|_U,x` of the stalks of the rings (`ExtensionByZeroModules.stalkResRingIso`),
  proved on germs (`ExtensionByZeroModules.restrictStalkIso_hom_smul`,
  `ExtensionByZeroModules.stalkHom_smul`), and is stated as an `𝒪_{X,x}`-linear equivalence onto
  `F_x` with scalars restricted along it.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite Limits

universe u

namespace ExtensionByZeroModules

attribute [local implicit_reducible] CategoryTheory.Functor.sheafPushforwardContinuous

variable {X : TopCat.{u}} (U : Opens X)
  (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- Two parallel morphisms in the opposite of the poset of opens of a space are equal. -/
lemma opensOp_hom_ext {Y : TopCat.{u}} {a b : (Opens Y)ᵒᵖ} (f g : a ⟶ b) : f = g :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

/-- The preimage `j⁻¹ V` in `U` of an open `V` of `X`. -/
abbrev preim (V : Opens X) : Opens (Usp U) := (Opens.map U.inclusion').obj V

/-- `j(j⁻¹ V) ⊆ V`. -/
lemma imF_preim_le (V : Opens X) : (TopCat.Presheaf.imF U).obj (preim U V) ≤ V := by
  rintro _ ⟨y, hy, rfl⟩
  exact hy

/-- `V ⊆ j(j⁻¹ V)` when `V ⊆ U`. -/
lemma le_imF_preim {V : Opens X} (hV : V ≤ U) : V ≤ (TopCat.Presheaf.imF U).obj (preim U V) :=
  fun x hx => ⟨⟨x, hV hx⟩, hx, rfl⟩

/-- `j⁻¹(j W) ⊆ W` for an open `W` of `U`. -/
lemma preim_imF_le (W : Opens (Usp U)) : preim U ((TopCat.Presheaf.imF U).obj W) ≤ W :=
  (Opens.map_functor_eq W).le

/-- The restriction `𝒪(V) → 𝒪(j(j⁻¹ V)) = 𝒪|_U(j⁻¹ V)`. -/
noncomputable def ringRes (V : Opens X) :
    O.obj.obj (op V) ⟶ (resRing U O).obj.obj (op (preim U V)) :=
  O.obj.map (homOfLE (imF_preim_le U V)).op

lemma resRing_map {a b : (Opens (Usp U))ᵒᵖ} (g : a ⟶ b) :
    (resRing U O).obj.map g = O.obj.map ((TopCat.Presheaf.imF U).map g.unop).op :=
  rfl

/-- Composites of restriction maps of a presheaf of rings on `X` only depend on the end points. -/
lemma ring_map_map {a b c : (Opens X)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) (h : a ⟶ c)
    (r : O.obj.obj a) : (O.obj.map g).hom ((O.obj.map f).hom r) = (O.obj.map h).hom r := by
  rw [← RingHom.comp_apply, ← RingCat.hom_comp, ← Functor.map_comp, opensOp_hom_ext (f ≫ g) h]

/-- Two parallel restriction maps of a presheaf of rings on `X` agree. -/
lemma ring_map_eq {a b : (Opens X)ᵒᵖ} (f g : a ⟶ b) (r : O.obj.obj a) :
    (O.obj.map f).hom r = (O.obj.map g).hom r := by
  rw [opensOp_hom_ext f g]

/-- An endomorphism restriction of a presheaf of rings on `X` is the identity. -/
lemma ring_map_self {a : (Opens X)ᵒᵖ} (f : a ⟶ a) (r : O.obj.obj a) : (O.obj.map f).hom r = r := by
  rw [opensOp_hom_ext f (𝟙 a), O.obj.map_id]
  rfl

variable {U O}

/-- Composites of restriction maps of a presheaf of modules on `U` only depend on the end points. -/
lemma mod_map_map (F : PresheafOfModules.{u} (resRing U O).obj) {a b c : (Opens (Usp U))ᵒᵖ}
    (f : a ⟶ b) (g : b ⟶ c) (h : a ⟶ c) (x : F.obj a) : F.map g (F.map f x) = F.map h x := by
  rw [← PresheafOfModules.map_comp_apply, opensOp_hom_ext (f ≫ g) h]

/-- Composites of restriction maps of a presheaf of modules on `X` only depend on the end points. -/
lemma modX_map_map (G : PresheafOfModules.{u} O.obj) {a b c : (Opens X)ᵒᵖ}
    (f : a ⟶ b) (g : b ⟶ c) (h : a ⟶ c) (x : G.obj a) : G.map g (G.map f x) = G.map h x := by
  rw [← PresheafOfModules.map_comp_apply, opensOp_hom_ext (f ≫ g) h]

/-- An endomorphism restriction of a presheaf of modules on `X` is the identity. -/
lemma modX_map_self (G : PresheafOfModules.{u} O.obj) {a : (Opens X)ᵒᵖ} (f : a ⟶ a)
    (x : G.obj a) : G.map f x = x := by
  change (G.presheaf.map f).hom x = x
  rw [opensOp_hom_ext f (𝟙 a), G.presheaf.map_id]
  rfl

/-- An endomorphism restriction of a presheaf of modules on `U` is the identity. -/
lemma mod_map_self (F : PresheafOfModules.{u} (resRing U O).obj) {a : (Opens (Usp U))ᵒᵖ}
    (f : a ⟶ a) (x : F.obj a) : F.map f x = x := by
  change (F.presheaf.map f).hom x = x
  rw [opensOp_hom_ext f (𝟙 a), F.presheaf.map_id]
  rfl

/-- Two composites of restriction maps of a presheaf of modules on `U` with the same end points
agree. -/
lemma mod_map_map_eq (F : PresheafOfModules.{u} (resRing U O).obj) {a b b' c : (Opens (Usp U))ᵒᵖ}
    (f : a ⟶ b) (g : b ⟶ c) (f' : a ⟶ b') (g' : b' ⟶ c) (x : F.obj a) :
    F.map g (F.map f x) = F.map g' (F.map f' x) := by
  rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply,
    opensOp_hom_ext (f ≫ g) (f' ≫ g')]

/-- Two composites of restriction maps of a presheaf of modules on `X` with the same end points
agree. -/
lemma modX_map_map_eq (G : PresheafOfModules.{u} O.obj) {a b b' c : (Opens X)ᵒᵖ}
    (f : a ⟶ b) (g : b ⟶ c) (f' : a ⟶ b') (g' : b' ⟶ c) (x : G.obj a) :
    G.map g (G.map f x) = G.map g' (G.map f' x) := by
  rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply,
    opensOp_hom_ext (f ≫ g) (f' ≫ g')]

/-- A restriction map of a presheaf of modules on `U` followed by one back is the identity. -/
lemma mod_map_map_self (F : PresheafOfModules.{u} (resRing U O).obj) {a b : (Opens (Usp U))ᵒᵖ}
    (f : a ⟶ b) (g : b ⟶ a) (x : F.obj a) : F.map g (F.map f x) = x :=
  (mod_map_map F f g (𝟙 a) x).trans (mod_map_self F _ x)

/-- A restriction map of a presheaf of modules on `X` followed by one back is the identity. -/
lemma modX_map_map_self (G : PresheafOfModules.{u} O.obj) {a b : (Opens X)ᵒᵖ}
    (f : a ⟶ b) (g : b ⟶ a) (x : G.obj a) : G.map g (G.map f x) = x :=
  (modX_map_map G f g (𝟙 a) x).trans (modX_map_self G _ x)

variable (U O)

/-- The sections over an open `V` of `X` of the extension by zero of `F`: the functions from the
proofs of `V ⊆ U` to `F(j⁻¹ V)`. This is `F(j⁻¹ V)` if `V ⊆ U` and the zero module otherwise. -/
abbrev ExtSec (F : PresheafOfModules.{u} (resRing U O).obj) (V : Opens X) : Type u :=
  PLift (V ≤ U) → F.obj (op (preim U V))

/-- `𝒪(V)` acts on `ExtSec U O F V` through the restriction `𝒪(V) → 𝒪|_U(j⁻¹ V)`. -/
noncomputable instance instModuleExtSec (F : PresheafOfModules.{u} (resRing U O).obj)
    (V : Opens X) : Module (O.obj.obj (op V)) (ExtSec U O F V) :=
  Module.compHom _ (ringRes U O V).hom

/-- The same action, indexed by an object of `(Opens X)ᵒᵖ`. -/
noncomputable instance instModuleExtSec' (F : PresheafOfModules.{u} (resRing U O).obj)
    (V : (Opens X)ᵒᵖ) : Module (O.obj.obj V) (ExtSec U O F V.unop) :=
  instModuleExtSec U O F V.unop

lemma extSec_smul_apply (F : PresheafOfModules.{u} (resRing U O).obj) {V : (Opens X)ᵒᵖ}
    (r : O.obj.obj V) (s : ExtSec U O F V.unop) (h : PLift (V.unop ≤ U)) :
    (r • s) h = (ringRes U O V.unop).hom r • s h :=
  rfl

/-- The module of sections over `V` of the extension by zero. -/
noncomputable abbrev extObj (F : PresheafOfModules.{u} (resRing U O).obj) (V : (Opens X)ᵒᵖ) :
    ModuleCat.{u} (O.obj.obj V) :=
  ModuleCat.of _ (ExtSec U O F V.unop)

lemma ringRes_comp {V W : (Opens X)ᵒᵖ} (f : V ⟶ W) (r : O.obj.obj V) :
    ((resRing U O).obj.map ((Opens.map U.inclusion').map f.unop).op).hom
        ((ringRes U O V.unop).hom r) =
      (ringRes U O W.unop).hom ((O.obj.map f).hom r) :=
  (ring_map_map O _ _ (f ≫ (homOfLE (imF_preim_le U W.unop)).op) r).trans
    (ring_map_map O _ _ _ r).symm

/-- The restriction maps of the extension by zero, as functions: the restriction of `F` when the
larger open lies in `U`, and zero otherwise. -/
noncomputable def extFun (F : PresheafOfModules.{u} (resRing U O).obj) {V W : (Opens X)ᵒᵖ}
    (f : V ⟶ W) (s : ExtSec U O F V.unop) : ExtSec U O F W.unop := fun _ =>
  open Classical in
  if h' : V.unop ≤ U then F.map ((Opens.map U.inclusion').map f.unop).op (s ⟨h'⟩) else 0

lemma extFun_of_le (F : PresheafOfModules.{u} (resRing U O).obj) {V W : (Opens X)ᵒᵖ}
    (f : V ⟶ W) (s : ExtSec U O F V.unop) (h : PLift (W.unop ≤ U)) (hV : V.unop ≤ U) :
    extFun U O F f s h = F.map ((Opens.map U.inclusion').map f.unop).op (s ⟨hV⟩) :=
  dite_eq_left hV

lemma extFun_of_not_le (F : PresheafOfModules.{u} (resRing U O).obj) {V W : (Opens X)ᵒᵖ}
    (f : V ⟶ W) (s : ExtSec U O F V.unop) (h : PLift (W.unop ≤ U)) (hV : ¬ V.unop ≤ U) :
    extFun U O F f s h = 0 :=
  dite_eq_right hV

/-- The restriction maps of the extension by zero, as semilinear maps. -/
noncomputable def extMap (F : PresheafOfModules.{u} (resRing U O).obj) {V W : (Opens X)ᵒᵖ}
    (f : V ⟶ W) :
    extObj U O F V ⟶ (ModuleCat.restrictScalars (O.obj.map f).hom).obj (extObj U O F W) :=
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars (O.obj.map f).hom).obj (extObj U O F W))
    { toFun := extFun U O F f
      map_add' := fun s t => funext fun h => by
        change extFun U O F f (s + t) h = extFun U O F f s h + extFun U O F f t h
        by_cases hV : V.unop ≤ U
        · rw [extFun_of_le U O F f _ h hV, extFun_of_le U O F f _ h hV,
            extFun_of_le U O F f _ h hV]
          exact map_add _ _ _
        · rw [extFun_of_not_le U O F f _ h hV, extFun_of_not_le U O F f _ h hV,
            extFun_of_not_le U O F f _ h hV, add_zero]
      map_smul' := fun r s => funext fun h => by
        change extFun U O F f (r • s) h =
          (ringRes U O W.unop).hom ((O.obj.map f).hom r) • extFun U O F f s h
        by_cases hV : V.unop ≤ U
        · rw [extFun_of_le U O F f _ h hV, extFun_of_le U O F f _ h hV, extSec_smul_apply,
            PresheafOfModules.map_smul, ringRes_comp]
          rfl
        · rw [extFun_of_not_le U O F f _ h hV, extFun_of_not_le U O F f _ h hV, smul_zero] }

lemma extMap_apply (F : PresheafOfModules.{u} (resRing U O).obj) {V W : (Opens X)ᵒᵖ}
    (f : V ⟶ W) (s : ExtSec U O F V.unop) : (extMap U O F f).hom s = extFun U O F f s :=
  rfl

/-- **The extension by zero `j_{p!}F` of a presheaf of `𝒪|_U`-modules** (Stacks 00A4, (5)), a
presheaf of `𝒪`-modules on `X`: its sections over `V` are `F(V)` (that is, `F(j⁻¹ V)`) if `V ⊆ U`
and `0` otherwise, with the restriction maps of `F` between opens contained in `U` and zero
restriction maps out of opens not contained in `U`. -/
noncomputable def extendByZeroObj (F : PresheafOfModules.{u} (resRing U O).obj) :
    PresheafOfModules.{u} O.obj where
  obj := extObj U O F
  map := extMap U O F
  map_id V := by
    refine ModuleCat.hom_ext (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _
      (fun (s : ExtSec U O F V.unop) => funext fun h => ?_))
    change extFun U O F (𝟙 V) s h = s h
    rw [extFun_of_le U O F _ s h h.down]
    exact mod_map_self F _ _
  map_comp {V W Z} f g := by
    refine ModuleCat.hom_ext (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _
      (fun (s : ExtSec U O F V.unop) => funext fun h => ?_))
    change extFun U O F (f ≫ g) s h = extFun U O F g (extFun U O F f s) h
    by_cases hV : V.unop ≤ U
    · have hW : W.unop ≤ U := (leOfHom f.unop).trans hV
      rw [extFun_of_le U O F _ s h hV, extFun_of_le U O F _ _ h hW,
        extFun_of_le U O F _ s ⟨hW⟩ hV]
      exact (mod_map_map F ((Opens.map U.inclusion').map f.unop).op
        ((Opens.map U.inclusion').map g.unop).op _ _).symm
    · rw [extFun_of_not_le U O F _ s h hV]
      by_cases hW : W.unop ≤ U
      · rw [extFun_of_le U O F _ _ h hW, extFun_of_not_le U O F _ s ⟨hW⟩ hV, map_zero]
        rfl
      · rw [extFun_of_not_le U O F _ _ h hW]

/-- The action of `j_{p!}` on morphisms: apply the morphism section by section. -/
noncomputable def extendByZeroMap {F F' : PresheafOfModules.{u} (resRing U O).obj} (η : F ⟶ F') :
    extendByZeroObj U O F ⟶ extendByZeroObj U O F' where
  app V := ModuleCat.ofHom
    { toFun := fun (s : ExtSec U O F V.unop) (h : PLift (V.unop ≤ U)) => η.app _ (s h)
      map_add' := fun s t => funext fun h => map_add (η.app _).hom (s h) (t h)
      map_smul' := fun r s => funext fun h => map_smul (η.app _).hom _ (s h) }
  naturality {V W} f := by
    refine ModuleCat.hom_ext (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _
      (fun (s : ExtSec U O F V.unop) => funext fun h => ?_))
    change η.app _ (extFun U O F f s h) = extFun U O F' f (fun h => η.app _ (s h)) h
    by_cases hV : V.unop ≤ U
    · rw [extFun_of_le U O F' _ _ h hV, extFun_of_le U O F _ _ h hV]
      exact PresheafOfModules.naturality_apply η _ _
    · rw [extFun_of_not_le U O F' _ _ h hV, extFun_of_not_le U O F _ _ h hV, map_zero]

/-- **Extension by zero** `j_{p!} : PMod(𝒪|_U) ⥤ PMod(𝒪)`, built explicitly as in Stacks 00A4
(5): `j_{p!}F(V) = F(V)` if `V ⊆ U` and `0` otherwise. -/
noncomputable def extendByZero :
    PresheafOfModules.{u} (resRing U O).obj ⥤ PresheafOfModules.{u} O.obj where
  obj := extendByZeroObj U O
  map := extendByZeroMap U O
  map_id _ := rfl
  map_comp _ _ := rfl

lemma extendByZero_map_apply (F : PresheafOfModules.{u} (resRing U O).obj)
    {V W : (Opens X)ᵒᵖ} (f : V ⟶ W) (s : ExtSec U O F V.unop) :
    ((extendByZero U O).obj F).map f s = extFun U O F f s :=
  rfl

/-- Over an open `V ⊄ U`, the extension by zero has no nonzero sections. -/
lemma isZero_extendByZero_obj (F : PresheafOfModules.{u} (resRing U O).obj) {V : Opens X}
    (hV : ¬ V ≤ U) : IsZero (((extendByZero U O).obj F).obj (op V)) := by
  have : Subsingleton (ExtSec U O F V) := ⟨fun s t => funext fun h => absurd h.down hV⟩
  exact ModuleCat.isZero_of_subsingleton (extObj U O F (op V))

/-- Over an open `V ⊆ U`, the sections of the extension by zero are the sections of `F` over `V`,
viewed as the open `j⁻¹ V` of `U`. -/
noncomputable def extendByZeroObjEquiv (F : PresheafOfModules.{u} (resRing U O).obj) {V : Opens X}
    (hV : V ≤ U) : ExtSec U O F V ≃+ F.obj (op (preim U V)) where
  toFun s := s ⟨hV⟩
  invFun t := fun _ => t
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-! ### `j_{p!}` is left adjoint to restriction -/

variable {U O}

/-- A section of `F` over an open `W` of `U`, as a section of `j_{p!}F` over `j(W)`. -/
noncomputable def inclSec (F : PresheafOfModules.{u} (resRing U O).obj) (W : Opens (Usp U))
    (t : F.obj (op W)) : ExtSec U O F ((TopCat.Presheaf.imF U).obj W) :=
  fun _ => F.map (homOfLE (preim_imF_le U W)).op t

/-- The function underlying `Hom(j_{p!}F, G) → Hom(F, G|_U)` over an open `W` of `U`. -/
noncomputable def toRestrictFun {F : PresheafOfModules.{u} (resRing U O).obj}
    {G : PresheafOfModules.{u} O.obj} (φ : (extendByZero U O).obj F ⟶ G) (W : Opens (Usp U))
    (t : F.obj (op W)) : G.obj (op ((TopCat.Presheaf.imF U).obj W)) :=
  φ.app (op ((TopCat.Presheaf.imF U).obj W)) (inclSec F W t)

/-- `inclSec` is compatible with restriction. -/
lemma inclSec_naturality (F : PresheafOfModules.{u} (resRing U O).obj)
    {W W' : (Opens (Usp U))ᵒᵖ} (g : W ⟶ W') (t : F.obj W) :
    inclSec F W'.unop (F.map g t) =
      extFun U O F ((TopCat.Presheaf.imF U).map g.unop).op (inclSec F W.unop t) := by
  funext h
  rw [extFun_of_le U O F _ _ h (imF_le U _)]
  exact mod_map_map_eq F g _ _ _ t

/-- `inclSec` is compatible with the action of `𝒪|_U(W) = 𝒪(j(W))`. -/
lemma inclSec_smul (F : PresheafOfModules.{u} (resRing U O).obj) (W : Opens (Usp U))
    (r : (resRing U O).obj.obj (op W)) (t : F.obj (op W)) :
    inclSec F W (r • t) =
      (id r : O.obj.obj (op ((TopCat.Presheaf.imF U).obj W))) • inclSec F W t :=
  funext fun _ => (PresheafOfModules.map_smul F _ r t).trans
    (congrArg (fun a => a • F.map (homOfLE (preim_imF_le U W)).op t) (ring_map_eq O _ _ r))

/-- The map `Hom(j_{p!}F, G) → Hom(F, G|_U)`. -/
noncomputable def toRestrict {F : PresheafOfModules.{u} (resRing U O).obj}
    {G : PresheafOfModules.{u} O.obj} (φ : (extendByZero U O).obj F ⟶ G) :
    F ⟶ (jpStar U O).obj G where
  app W := ModuleCat.ofHom (Y := ((jpStar U O).obj G).obj W)
    { toFun := toRestrictFun φ W.unop
      map_add' := fun t t' =>
        (congrArg (φ.app (op ((TopCat.Presheaf.imF U).obj W.unop))).hom
          (funext fun _ => map_add _ t t' :
            inclSec F W.unop (t + t') = inclSec F W.unop t + inclSec F W.unop t')).trans
          (map_add _ _ _)
      map_smul' := fun r t =>
        (congrArg (φ.app (op ((TopCat.Presheaf.imF U).obj W.unop))).hom
          (inclSec_smul F W.unop r t)).trans (map_smul _ _ _) }
  naturality {W W'} g := by
    refine ModuleCat.hom_ext (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _
      (fun (t : F.obj W) => ?_))
    exact (congrArg (φ.app (op ((TopCat.Presheaf.imF U).obj W'.unop))).hom
      (inclSec_naturality F g t)).trans (PresheafOfModules.naturality_apply φ _ _)

/-- The function underlying `Hom(F, G|_U) → Hom(j_{p!}F, G)` over an open `V` of `X`: over
`V ⊆ U` it is `ψ`, and over the other opens it is zero. -/
noncomputable def fromRestrictFun {F : PresheafOfModules.{u} (resRing U O).obj}
    {G : PresheafOfModules.{u} O.obj} (ψ : F ⟶ (jpStar U O).obj G) (V : Opens X)
    (s : ExtSec U O F V) : G.obj (op V) :=
  open Classical in
  if h : V ≤ U then G.map (homOfLE (le_imF_preim U h)).op (ψ.app (op (preim U V)) (s ⟨h⟩))
  else 0

lemma fromRestrictFun_of_le {F : PresheafOfModules.{u} (resRing U O).obj}
    {G : PresheafOfModules.{u} O.obj} (ψ : F ⟶ (jpStar U O).obj G) {V : Opens X}
    (s : ExtSec U O F V) (h : V ≤ U) :
    fromRestrictFun ψ V s =
      G.map (homOfLE (le_imF_preim U h)).op (ψ.app (op (preim U V)) (s ⟨h⟩)) :=
  dite_eq_left h

lemma fromRestrictFun_of_not_le {F : PresheafOfModules.{u} (resRing U O).obj}
    {G : PresheafOfModules.{u} O.obj} (ψ : F ⟶ (jpStar U O).obj G) {V : Opens X}
    (s : ExtSec U O F V) (h : ¬ V ≤ U) : fromRestrictFun ψ V s = 0 :=
  dite_eq_right h

/-- The map `Hom(F, G|_U) → Hom(j_{p!}F, G)`. -/
noncomputable def fromRestrict {F : PresheafOfModules.{u} (resRing U O).obj}
    {G : PresheafOfModules.{u} O.obj} (ψ : F ⟶ (jpStar U O).obj G) :
    (extendByZero U O).obj F ⟶ G where
  app V := ModuleCat.ofHom
    { toFun := fromRestrictFun ψ V.unop
      map_add' := fun s t => by
        by_cases h : V.unop ≤ U
        · rw [fromRestrictFun_of_le ψ _ h, fromRestrictFun_of_le ψ _ h,
            fromRestrictFun_of_le ψ _ h]
          exact (congrArg (fun y => G.map (homOfLE (le_imF_preim U h)).op y)
            (map_add (ψ.app _).hom _ _)).trans (map_add _ _ _)
        · rw [fromRestrictFun_of_not_le ψ _ h, fromRestrictFun_of_not_le ψ _ h,
            fromRestrictFun_of_not_le ψ _ h, add_zero]
      map_smul' := fun r s => by
        by_cases h : V.unop ≤ U
        · rw [fromRestrictFun_of_le ψ _ h, fromRestrictFun_of_le ψ _ h]
          refine (congrArg (fun y => G.map (homOfLE (le_imF_preim U h)).op y)
            (map_smul (ψ.app (op (preim U V.unop))).hom ((ringRes U O V.unop).hom r)
              (s ⟨h⟩))).trans ?_
          refine (G.map_smul _ _ _).trans ?_
          congr 1
          exact (ring_map_map O _ _ (𝟙 _) r).trans (ring_map_self O _ r)
        · rw [fromRestrictFun_of_not_le ψ _ h, fromRestrictFun_of_not_le ψ _ h, smul_zero] }
  naturality {V W} f := by
    refine ModuleCat.hom_ext (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _
      (fun (s : ExtSec U O F V.unop) => ?_))
    change fromRestrictFun ψ W.unop (extFun U O F f s) = G.map f (fromRestrictFun ψ V.unop s)
    by_cases hV : V.unop ≤ U
    · have hW : W.unop ≤ U := (leOfHom f.unop).trans hV
      rw [fromRestrictFun_of_le ψ _ hW, fromRestrictFun_of_le ψ _ hV,
        extFun_of_le U O F f s ⟨hW⟩ hV, PresheafOfModules.naturality_apply]
      exact modX_map_map_eq G _ _ _ _ _
    · rw [fromRestrictFun_of_not_le ψ _ hV, map_zero]
      by_cases hW : W.unop ≤ U
      · rw [fromRestrictFun_of_le ψ _ hW, extFun_of_not_le U O F f s ⟨hW⟩ hV, map_zero]
        exact map_zero (G.map (homOfLE (le_imF_preim U hW)).op).hom
      · rw [fromRestrictFun_of_not_le ψ _ hW]
        rfl

/-- Restricting `inclSec` of a section back to an open `V ⊆ U` recovers it. -/
lemma extFun_inclSec_preim (F : PresheafOfModules.{u} (resRing U O).obj) {V : Opens X}
    (h : V ≤ U) (x : F.obj (op (preim U V))) :
    extFun U O F (homOfLE (le_imF_preim U h)).op (inclSec F (preim U V) x) = fun _ => x := by
  funext h2
  rw [extFun_of_le U O F _ _ h2 (imF_le U _)]
  exact mod_map_map_self F _ _ x

lemma fromRestrictFun_toRestrict {F : PresheafOfModules.{u} (resRing U O).obj}
    {G : PresheafOfModules.{u} O.obj} (φ : (extendByZero U O).obj F ⟶ G) (V : Opens X)
    (s : ExtSec U O F V) : fromRestrictFun (toRestrict φ) V s = φ.app (op V) s := by
  by_cases h : V ≤ U
  · rw [fromRestrictFun_of_le _ _ h]
    have hs : (fun _ => s ⟨h⟩ : ExtSec U O F V) = s := funext fun _ => rfl
    exact (PresheafOfModules.naturality_apply φ (homOfLE (le_imF_preim U h)).op
      (inclSec F (preim U V) (s ⟨h⟩))).symm.trans
        (congrArg (φ.app (op V)).hom ((extFun_inclSec_preim F h (s ⟨h⟩)).trans hs))
  · rw [fromRestrictFun_of_not_le _ _ h]
    have hs : s = 0 := funext fun h2 => absurd h2.down h
    rw [hs]
    exact (map_zero (φ.app (op V)).hom).symm

lemma fromRestrict_toRestrict {F : PresheafOfModules.{u} (resRing U O).obj}
    {G : PresheafOfModules.{u} O.obj} (φ : (extendByZero U O).obj F ⟶ G) :
    fromRestrict (toRestrict φ) = φ :=
  PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_)
    _ _ _ (fun (s : ExtSec U O F V.unop) => fromRestrictFun_toRestrict φ V.unop s))

lemma toRestrictFun_fromRestrict {F : PresheafOfModules.{u} (resRing U O).obj}
    {G : PresheafOfModules.{u} O.obj} (ψ : F ⟶ (jpStar U O).obj G) (W : Opens (Usp U))
    (t : F.obj (op W)) : toRestrictFun (fromRestrict ψ) W t = ψ.app (op W) t := by
  change fromRestrictFun ψ ((TopCat.Presheaf.imF U).obj W) (inclSec F W t) = ψ.app (op W) t
  rw [fromRestrictFun_of_le _ _ (imF_le U _)]
  exact (congrArg (G.map (homOfLE (le_imF_preim U (imF_le U W))).op).hom
    (PresheafOfModules.naturality_apply ψ (homOfLE (preim_imF_le U W)).op t)).trans
      (modX_map_map_self G _ _ _)

lemma toRestrict_fromRestrict {F : PresheafOfModules.{u} (resRing U O).obj}
    {G : PresheafOfModules.{u} O.obj} (ψ : F ⟶ (jpStar U O).obj G) :
    toRestrict (fromRestrict ψ) = ψ :=
  PresheafOfModules.hom_ext fun W => ModuleCat.hom_ext (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_)
    _ _ _ (fun (t : F.obj W) => toRestrictFun_fromRestrict ψ W.unop t))

variable (U O)

/-- **Stacks 00A7 (1).** The explicit extension by zero `j_{p!}` of presheaves of modules
(`V ↦ F(V)` for `V ⊆ U`, `V ↦ 0` otherwise, `ExtensionByZeroModules.extendByZero`) is left adjoint
to the restriction functor `PMod(𝒪) ⥤ PMod(𝒪|_U)`, `G ↦ G|_U`: `Hom(j_{p!}F, G) = Hom(F, G|_U)`,
naturally in `F` and `G`. The bijection sends `φ` to `t ↦ φ(t)` over opens of `U`, and `ψ` to
the map which is `ψ` over opens `V ⊆ U` and zero over the other opens. -/
@[stacks 00A7 "(1): `j_{p!}` is the explicit extension by zero of presheaves of modules"]
noncomputable def extendByZeroAdjunction : extendByZero U O ⊣ jpStar U O :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
        { toFun := toRestrict
          invFun := fromRestrict
          left_inv := fromRestrict_toRestrict
          right_inv := toRestrict_fromRestrict }
      homEquiv_naturality_left_symm := fun _ _ => rfl
      homEquiv_naturality_right := fun _ _ => rfl }

/-- The explicit extension by zero is isomorphic to Mathlib's abstract left adjoint
`PresheafOfModules.pullback` of the restriction functor. -/
noncomputable def extendByZeroIsoJpShriek : extendByZero U O ≅ jpShriek U O :=
  (extendByZeroAdjunction U O).leftAdjointUniq
    (PresheafOfModules.pullbackPushforwardAdjunction _)

/-! ### Extension by zero of sheaves of modules -/

/-- **Extension by zero of sheaves of modules** (Stacks 00A4 (5)), `j_! F`, the sheafification
of the explicit presheaf extension by zero `j_{p!} F` of the underlying presheaf of `F`. -/
noncomputable def jShriekExplicit : SheafOfModules.{u} (resRing U O) ⥤ SheafOfModules.{u} O :=
  SheafOfModules.forget _ ⋙ extendByZero U O ⋙ PresheafOfModules.sheafification (𝟙 O.obj)

/-- The sheafified explicit extension by zero is isomorphic to Mathlib's abstract left adjoint
`SheafOfModules.pullback` of restriction, i.e. to `ExtensionByZeroModules.jShriek`. -/
noncomputable def jShriekExplicitIso : jShriekExplicit U O ≅ jShriek U O :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (extendByZeroIsoJpShriek U O) _) ≪≫
    (SheafOfModules.pullbackIso (𝟙 (resRing U O))).symm

/-- **Stacks 00A7 (2).** Extension by zero `j_!` of sheaves of modules, the sheafification of the
explicit `j_{p!}`, is left adjoint to the restriction functor `Mod(𝒪) ⥤ Mod(𝒪|_U)`:
`Hom(j_!F, G) = Hom(F, G|_U)`, naturally in `F` and `G`. It is obtained from the adjunction of (1)
and the sheafification adjunction, through the identification `jShriekExplicitIso`. -/
@[stacks 00A7 "(2): `j_!` is the sheafification of the explicit `j_{p!}`"]
noncomputable def jShriekExplicitAdjunction : jShriekExplicit U O ⊣ jStar U O :=
  (jShriekAdjunction U O).ofNatIsoLeft (jShriekExplicitIso U O).symm

/-- **Stacks 00A7 (3), points outside `U`.** For a sheaf `F` of `𝒪|_U`-modules and `x ∉ U`, the
stalk `(j_!F)_x` is zero. The statement is about the underlying abelian group of the
`𝒪_{X,x}`-module `(j_!F)_x`, which vanishes exactly when the module does. -/
@[stacks 00A7 "(3), the stalk of `j_!F` at `x ∉ U` is zero"]
theorem isZero_stalk_jShriekExplicit (F : SheafOfModules.{u} (resRing U O)) (x : X) (hx : x ∉ U) :
    IsZero (TopCat.Presheaf.stalk (X := X) ((jShriekExplicit U O).obj F).val.presheaf x) :=
  (isZero_stalk_jShriek U O F x hx).of_iso
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
      ((toAb O).mapIso ((jShriekExplicitIso U O).app F)))

/-- For a sheaf `F` of `𝒪|_U`-modules and `x ∈ U`, the stalk `(j_!F)_x` is the stalk `F_x`, as
abelian groups. The `𝒪_{X,x}`-linear version, which is Stacks 00A7 (3), is
`ExtensionByZeroModules.stalkJShriekExplicitLinearEquiv`. -/
noncomputable def stalkJShriekExplicitIso (F : SheafOfModules.{u} (resRing U O)) (x : X)
    (hx : x ∈ U) :
    TopCat.Presheaf.stalk (X := X) ((jShriekExplicit U O).obj F).val.presheaf x ≅
      TopCat.Presheaf.stalk (X := Usp U) F.val.presheaf ⟨x, hx⟩ :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
      ((toAb O).mapIso ((jShriekExplicitIso U O).app F)) ≪≫
    stalkJShriekIso U O F x hx

/-- **Stacks 00A7 (4).** `j^{-1} j_! = id` on sheaves of `𝒪|_U`-modules: restricting the extension
by zero of `F` back to `U` gives `F`, naturally in `F`. -/
@[stacks 00A7 "(4): `j^{-1} j_! ≅ id` on sheaves of `𝒪|_U`-modules"]
noncomputable def jShriekExplicitCompJStarIso :
    jShriekExplicit U O ⋙ jStar U O ≅ 𝟭 (SheafOfModules.{u} (resRing U O)) :=
  haveI := isIso_jShriekAdjunction_unit U O
  Functor.isoWhiskerRight (jShriekExplicitIso U O) (jStar U O) ≪≫
    (asIso (jShriekAdjunction U O).unit).symm

/-! ### Stalks of `j_!F` at points of `U`, as modules -/

/-- Two elements of stalks at `y` of a presheaf of rings and of an abelian presheaf are germs of
sections over a common open neighbourhood of `y`. -/
lemma exists_germ_pair {Y : TopCat.{u}} (P : TopCat.Presheaf RingCat.{u} Y)
    (Q : TopCat.Presheaf AddCommGrpCat.{u} Y) {y : Y} (r : P.stalk y) (m : Q.stalk y) :
    ∃ (V : Opens Y) (hy : y ∈ V) (r₀ : P.obj (op V)) (m₀ : Q.obj (op V)),
      P.germ V y hy r₀ = r ∧ Q.germ V y hy m₀ = m := by
  obtain ⟨V, hV, r₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq P r
  obtain ⟨W, hW, m₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq Q m
  exact ⟨V ⊓ W, ⟨hV, hW⟩, P.map (homOfLE inf_le_left).op r₀, Q.map (homOfLE inf_le_right).op m₀,
    TopCat.Presheaf.germ_res_apply P _ y _ r₀, TopCat.Presheaf.germ_res_apply Q _ y _ m₀⟩

/-- The map on stalks at `y` induced by a morphism of presheaves of modules, as a morphism of the
underlying abelian groups. -/
noncomputable def stalkHom {Y : TopCat.{u}} {R : TopCat.Presheaf RingCat.{u} Y}
    {M N : PresheafOfModules.{u} R} (f : M ⟶ N) (y : Y) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := Y) M.presheaf y ⟶
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := Y) N.presheaf y :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map ((PresheafOfModules.toPresheaf R).map f)

/-- The isomorphism of stalks induced by an isomorphism of presheaves of modules. -/
noncomputable def stalkIso {Y : TopCat.{u}} {R : TopCat.Presheaf RingCat.{u} Y}
    {M N : PresheafOfModules.{u} R} (e : M ≅ N) (y : Y) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := Y) M.presheaf y ≅
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := Y) N.presheaf y :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).mapIso
    ((PresheafOfModules.toPresheaf R).mapIso e)

lemma stalkIso_hom {Y : TopCat.{u}} {R : TopCat.Presheaf RingCat.{u} Y}
    {M N : PresheafOfModules.{u} R} (e : M ≅ N) (y : Y) :
    (stalkIso e y).hom = stalkHom e.hom y :=
  rfl

lemma stalkHom_germ {Y : TopCat.{u}} {R : TopCat.Presheaf RingCat.{u} Y}
    {M N : PresheafOfModules.{u} R} (f : M ⟶ N) (y : Y) (V : Opens Y) (hy : y ∈ V)
    (s : M.obj (op V)) :
    stalkHom f y (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.presheaf V y hy s) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) N.presheaf V y hy (f.app (op V) s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply V y hy ((PresheafOfModules.toPresheaf R).map f) s

/-- The map on stalks induced by a morphism of presheaves of modules is linear over the stalk of
the ring. -/
lemma stalkHom_smul {Y : TopCat.{u}} {R : TopCat.Presheaf RingCat.{u} Y}
    {M N : PresheafOfModules.{u} R} (f : M ⟶ N) (y : Y)
    (r : TopCat.Presheaf.stalk (C := RingCat.{u}) (X := Y) R y)
    (m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := Y) M.presheaf y) :
    stalkHom f y (r • m) = r • stalkHom f y m := by
  obtain ⟨V, hy, r₀, m₀, rfl, rfl⟩ := exists_germ_pair R M.presheaf r m
  exact (congrArg (stalkHom f y) (PresheafOfModules.germ_ringCat_smul M y V hy r₀ m₀).symm).trans
    ((stalkHom_germ f y V hy (r₀ • m₀)).trans
      ((congrArg (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) N.presheaf V y hy)
        ((f.app (op V)).hom.map_smul r₀ m₀)).trans
        ((PresheafOfModules.germ_ringCat_smul N y V hy r₀ (f.app (op V) m₀)).trans
          (congrArg (fun z => TopCat.Presheaf.germ (C := RingCat.{u}) R V y hy r₀ • z)
            (stalkHom_germ f y V hy m₀).symm))))

/-- The identification `(j⁻¹G)_u ≅ G_{j u}` of the stalk of the restriction of a sheaf of
`𝒪`-modules `G` to `U`. -/
noncomputable def restrictStalkIso (G : SheafOfModules.{u} O) (u : Usp U) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := Usp U)
        ((jStar U O).obj G).val.presheaf u ≅
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) G.val.presheaf (U.inclusion' u) :=
  TopCat.Presheaf.stalkRestrictIso U G.val.presheaf u

/-- The identification `𝒪|_U,u ≅ 𝒪_{X, j u}` of the ring stalks. -/
noncomputable def restrictRingStalkIso (u : Usp U) :
    TopCat.Presheaf.stalk (C := RingCat.{u}) (X := Usp U) (resRing U O).obj u ≅
      TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj (U.inclusion' u) :=
  TopCat.Presheaf.stalkRestrictIso U O.obj u

/-- The identification `𝒪_{X,x} ≅ 𝒪|_U,x` of the ring stalks at a point `x = j u` of `U`. -/
noncomputable def stalkResRingIso (u : Usp U) :
    TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj (U.inclusion' u) ≅
      TopCat.Presheaf.stalk (C := RingCat.{u}) (X := Usp U) (resRing U O).obj
        u :=
  (restrictRingStalkIso U O u).symm

/-- The identification `(j⁻¹G)_u ≅ G_{j u}` is semilinear along the identification
`𝒪|_U,u ≅ 𝒪_{X, j u}` of the ring stalks. -/
lemma restrictStalkIso_hom_smul (G : SheafOfModules.{u} O) (u : Usp U)
    (r : TopCat.Presheaf.stalk (C := RingCat.{u}) (X := Usp U) (resRing U O).obj u)
    (m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := Usp U)
      ((jStar U O).obj G).val.presheaf u) :
    (restrictStalkIso U O G u).hom (r • m) =
      (restrictRingStalkIso U O u).hom r • (restrictStalkIso U O G u).hom m := by
  obtain ⟨V, hu, r₀, m₀, rfl, rfl⟩ :=
    exists_germ_pair (resRing U O).obj ((jStar U O).obj G).val.presheaf r m
  have hx : U.inclusion' u ∈ (TopCat.Presheaf.imF U).obj V := ⟨u, hu, rfl⟩
  have keyM : ∀ s : ((jStar U O).obj G).val.obj (op V),
      (restrictStalkIso U O G u).hom (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          ((jStar U O).obj G).val.presheaf V u hu s) =
        TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) G.val.presheaf
          ((TopCat.Presheaf.imF U).obj V) (U.inclusion' u) hx s := fun s =>
    ConcreteCategory.congr_hom (TopCat.Presheaf.stalkRestrictIso_germ U G.val.presheaf V u hu) s
  have keyR : (restrictRingStalkIso U O u).hom (TopCat.Presheaf.germ (C := RingCat.{u})
        (resRing U O).obj V u hu r₀) =
      TopCat.Presheaf.germ (C := RingCat.{u}) O.obj ((TopCat.Presheaf.imF U).obj V)
        (U.inclusion' u) hx r₀ :=
    ConcreteCategory.congr_hom (TopCat.Presheaf.stalkRestrictIso_germ U O.obj V u hu) r₀
  exact (congrArg (restrictStalkIso U O G u).hom
      (PresheafOfModules.germ_ringCat_smul ((jStar U O).obj G).val u V hu r₀ m₀).symm).trans
    ((keyM (r₀ • m₀)).trans
      ((PresheafOfModules.germ_ringCat_smul G.val (U.inclusion' u)
        ((TopCat.Presheaf.imF U).obj V) hx r₀ m₀).trans
        (congrArg₂ (fun (a : TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj
            (U.inclusion' u))
          (b : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) G.val.presheaf
            (U.inclusion' u)) => a • b) keyR.symm (keyM m₀).symm)))

/-- The identification `(j_!F)_x ≅ F_x` at a point `x = j u` of `U` of the stalks, as abelian
groups, through
`j^{-1} j_! F ≅ F`. -/
noncomputable def stalkJShriekExplicitAddIso (F : SheafOfModules.{u} (resRing U O)) (u : Usp U) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X)
        ((jShriekExplicit U O).obj F).val.presheaf
          (U.inclusion' u) ≅
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := Usp U) F.val.presheaf u :=
  (restrictStalkIso U O ((jShriekExplicit U O).obj F) u).symm ≪≫
    stalkIso ((SheafOfModules.forget _).mapIso ((jShriekExplicitCompJStarIso U O).app F))
      u

/-- `stalkJShriekExplicitAddIso` is semilinear along `stalkResRingIso`. -/
lemma stalkJShriekExplicitAddIso_smul (F : SheafOfModules.{u} (resRing U O)) (u : Usp U)
    (r : TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj (U.inclusion' u))
    (m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X)
      ((jShriekExplicit U O).obj F).val.presheaf
          (U.inclusion' u)) :
    (stalkJShriekExplicitAddIso U O F u).hom (r • m) =
      (stalkResRingIso U O u).hom r • (stalkJShriekExplicitAddIso U O F u).hom m := by
  have h1 : (restrictStalkIso U O ((jShriekExplicit U O).obj F) u).inv (r • m) =
      (restrictRingStalkIso U O u).inv r •
        (restrictStalkIso U O ((jShriekExplicit U O).obj F) u).inv m := by
    apply (ConcreteCategory.bijective_of_isIso
      (restrictStalkIso U O ((jShriekExplicit U O).obj F) u).hom).1
    rw [restrictStalkIso_hom_smul U O _ u, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply,
      Iso.inv_hom_id_apply]
  change stalkHom ((SheafOfModules.forget _).map
      ((jShriekExplicitCompJStarIso U O).app F).hom) u
        ((restrictStalkIso U O ((jShriekExplicit U O).obj F) u).inv (r • m)) =
    (restrictRingStalkIso U O u).inv r • stalkHom ((SheafOfModules.forget _).map
      ((jShriekExplicitCompJStarIso U O).app F).hom) u
        ((restrictStalkIso U O ((jShriekExplicit U O).obj F) u).inv m)
  rw [h1]
  exact stalkHom_smul _ _ _ _

/-- **Stacks 00A7 (3), points of `U`.** For a sheaf `F` of `𝒪|_U`-modules and a point `x ∈ U`
(written `x = j u` with `u` the point `x` of the subspace `U`), the stalk `(j_!F)_x` is `F_x` as
modules. The stalk `(j_!F)_x` is an `𝒪_{X,x}`-module, `F_x` is an
`𝒪|_U,x`-module, and the identification is linear along the canonical isomorphism
`𝒪_{X,x} ≅ 𝒪|_U,x` (`stalkResRingIso`): it is an isomorphism of `𝒪_{X,x}`-modules from
`(j_!F)_x` to `F_x` with scalars restricted along that ring isomorphism. Its underlying additive
map is `stalkJShriekExplicitAddIso`. -/
@[stacks 00A7 "(3), the stalk of `j_!F` at `x ∈ U` is `F_x`, linearly over `𝒪_{X,x} ≅ 𝒪|_U,x`"]
noncomputable def stalkJShriekExplicitLinearEquiv (F : SheafOfModules.{u} (resRing U O))
    (u : Usp U) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X)
        ((jShriekExplicit U O).obj F).val.presheaf (U.inclusion' u) ≃ₗ[
          TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj (U.inclusion' u)]
      (ModuleCat.restrictScalars (stalkResRingIso U O u).hom.hom).obj
        (ModuleCat.of
          (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := Usp U) (resRing U O).obj u)
          (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := Usp U) F.val.presheaf u)) :=
  { (stalkJShriekExplicitAddIso U O F u).addCommGroupIsoToAddEquiv with
    map_smul' := fun r m => stalkJShriekExplicitAddIso_smul U O F u r m }

end ExtensionByZeroModules
