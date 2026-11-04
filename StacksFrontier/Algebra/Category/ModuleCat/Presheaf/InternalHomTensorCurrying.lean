module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomVariance
import StacksCore.Tactic.StacksAttribute

/-!
# Internal Hom out of a tensor product of presheaves of modules

Let `O` be a presheaf of commutative rings on a category `C` and let `F`, `G`, `H` be
presheaves of `O`-modules. One clause of Stacks 03EO is the currying isomorphism

`Hom_O(F ⊗_O G, H) ≅ Hom_O(F, Hom_O(G, H))`

of presheaves of `O`-modules, where `Hom_O` is the internal Hom presheaf of Stacks 03EM.

The proof is the usual currying of a bilinear map, carried out one slice at a time. A section
of the left-hand side over `U` is a morphism `(F ⊗ G)|_U ⟶ H|_U` on `C/U`; sending it to the
rule which takes `x ∈ F(X)` over `X ⟶ U` and `y ∈ G(Y)` over `Y ⟶ X` to its value on
`F(Y ⟶ X)(x) ⊗ y` produces a section of the right-hand side, and reading the construction
backwards — evaluate at the identity of the slice — inverts it. Both directions are
`O(U)`-linear and compatible with restriction, so they assemble into an isomorphism of
presheaves of modules.

## Main definitions

* `Stacks.PresheafOfModules.InternalHom.currySection` and `uncurrySection`: the two mutually
  inverse maps on sections over an object, with `currySectionLinearMap` recording the
  linearity of the first.

## Main results

* `Stacks.PresheafOfModules.InternalHom.presheafInternalHomTensorIso`: the currying
  isomorphism.
* `Stacks.PresheafOfModules.InternalHom.presheafInternalHomTensorIso_natural_left`,
  `..._natural_middle` and `..._natural_right`: its functoriality in the two tensor factors
  (contravariantly) and in the target (covariantly).
* `Stacks.PresheafOfModules.InternalHom.presheafInternalHomTensorIso_hom_app`: on sections it
  is ordinary tensor currying, which pins the isomorphism down.

## Implementation notes

The tensor product is Mathlib's objectwise monoidal product on presheaves of modules, so a
section of `(F ⊗ G)|_U` over `X ⟶ U` is literally an element of `F(X) ⊗_{O(X)} G(X)` — but
only after unfolding `restrFun`, and that unfolding is not available to instance search or to
`rw`. The slice of a slice makes this acute: a section reached by restricting twice has its
scalars spelled by the index route taken, and the two routes are definitionally but not
syntactically equal.

Rather than relax the ambient transparency, the retyping is **named once** and the whole
development is phrased through those names. `restrSection`/`sectionOfRestr` move a plain
section of `M` over `W` to and from a section of `M|_U` over `h : W ⟶ U`; `ofRestrHom` does the
same for morphisms; and `restrTensorHom` presents a slice-level
morphism out of a restricted tensor product as an honest `LinearMap` on an honest
`TensorProduct`. Each is a definition whose body is its own argument, so the identification is
checked once, at default transparency, where it is available. Downstream every `TensorProduct`
lemma, and `TensorProduct.lift`, applies with no friction, and Mathlib's
`PresheafOfModules.restrictₛₗ` supplies the same service for the restriction of an element.

The one step that needs care even so is the naturality of the isomorphism. The restriction
maps of the internal Hom presheaf are `homRestr`, which is built from `eqToHom` of opaque
`rfl` theorems; instantiating that at the internal Hom presheaf itself and asking the
elaborator to see through it exhausts the heartbeat budget. `homRestr_app_apply` states the
re-indexing generically, where the proof is cheap, and `currySection_homRestr` rewrites with
it instead.

Only the `presheaf_internal_hom_tensor_iso` clause of Stacks 03EO is proved here; the
tensor-Hom adjunction and the sheaf analogues are separate statements. That clause's covering set
is exactly `presheafInternalHomTensorIso`, `..._hom_app`, `..._natural_left`,
`..._natural_middle` and `..._natural_right`, which carry the tag; the retyping helpers and
the slice-level `currySection`/`uncurrySection` layer do not. All five carry the two
independent universes `v` and `u`, with the ring universe `max u v w`, and no narrowing.

## References

* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite

namespace Stacks.PresheafOfModules.InternalHom

universe v u w

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ CommRingCat.{max u v w})

/-- Iterated restriction of a section. -/
theorem restrictₛₗ_comp_apply (M : _root_.PresheafOfModules.{max u v w} (Oforget O)) {X Y Z : Cᵒᵖ}
    (i : X ⟶ Y) (j : Y ⟶ Z) (x : M.obj X) :
    M.restrictₛₗ (i ≫ j) x = M.restrictₛₗ j (M.restrictₛₗ i x) :=
  M.map_comp_apply i j x

/-- Restriction of a section is semilinear for the `CommRingCat`-valued structure presheaf. -/
theorem restrictₛₗ_smul (M : _root_.PresheafOfModules.{max u v w} (Oforget O)) {X Y : Cᵒᵖ}
    (f : X ⟶ Y) (r : O.obj X) (m : M.obj X) :
    M.restrictₛₗ f (r • m) = (O.map f).hom r • M.restrictₛₗ f m :=
  M.map_smul f r m

variable (M N : _root_.PresheafOfModules.{max u v w} (Oforget O))

/-- A section of `M` over `W`, read as a section of `M|_U` over `h : W ⟶ U`. -/
noncomputable def restrSection (U : C) {W : C} (h : W ⟶ U) (x : M.obj (op W)) :
    ((restrFun O U).obj M).obj (op (Over.mk h)) := x

/-- A section of `M|_U` over `h : W ⟶ U`, read as a section of `M` over `W`. -/
noncomputable def sectionOfRestr (U : C) {W : C} (h : W ⟶ U)
    (x : ((restrFun O U).obj M).obj (op (Over.mk h))) : M.obj (op W) := x

/-- A linear map of plain sections, read as a map of restricted sections. -/
noncomputable def ofRestrHom (U : C) (V : (Over U)ᵒᵖ)
    (b : M.obj (op V.unop.left) →ₗ[O.obj (op V.unop.left)] N.obj (op V.unop.left)) :
    ((restrFun O U).obj M).obj V ⟶ ((restrFun O U).obj N).obj V :=
  letI : Module ((ORestr O U).obj V) (((restrFun O U).obj M).obj V) :=
    (((restrFun O U).obj M).obj V).isModule
  letI : Module ((ORestr O U).obj V) (((restrFun O U).obj N).obj V) :=
    (((restrFun O U).obj N).obj V).isModule
  letI : AddCommGroup (((restrFun O U).obj M).obj V) :=
    (((restrFun O U).obj M).obj V).isAddCommGroup
  letI : AddCommGroup (((restrFun O U).obj N).obj V) :=
    (((restrFun O U).obj N).obj V).isAddCommGroup
  ConcreteCategory.ofHom (C := ModuleCat ((ORestr O U).obj V)) b

variable (F G H : _root_.PresheafOfModules.{max u v w} (Oforget O)) (U : C)

/-- A slice-level morphism out of a restricted tensor product, retyped at `h : W ⟶ U` as a
linear map on the honest tensor product of the plain sections over `W`. -/
noncomputable def restrTensorHom
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H) {W : C} (h : W ⟶ U) :
    TensorProduct (O.obj (op W)) (F.obj (op W)) (G.obj (op W)) →ₗ[O.obj (op W)]
      H.obj (op W) :=
  (a.app (op (Over.mk h))).hom

/-- A pure tensor of plain sections over `W`, as a section of `(F ⊗ G)|_U` over `h : W ⟶ U`. -/
noncomputable def restrTmul (U : C) {W : C} (h : W ⟶ U)
    (x : F.obj (op W)) (y : G.obj (op W)) :
    ((restrFun O U).obj (F ⊗ G)).obj (op (Over.mk h)) :=
  x ⊗ₜ[O.obj (op W)] y

/-- Naturality of a slice-level morphism, on pure tensors of plain sections. -/
theorem restrTensorHom_nat
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H) {W W' : C} (h : W ⟶ U)
    (k : W' ⟶ W) (x : F.obj (op W)) (y : G.obj (op W)) :
    restrTensorHom O F G H U a (k ≫ h)
        (F.restrictₛₗ k.op x ⊗ₜ G.restrictₛₗ k.op y) =
      H.restrictₛₗ k.op (restrTensorHom O F G H U a h (x ⊗ₜ y)) :=
  congrArg (sectionOfRestr O H U (k ≫ h))
    (_root_.PresheafOfModules.naturality_apply a
      ((Over.homMk k : (Over.mk (k ≫ h) : Over U) ⟶ Over.mk h).op)
      (restrTmul O F G U h x y))

/-- The curried map at the second slice depth: over `q : T ⟶ S`, send `y` to the value of
`a` on the restriction of `x` tensored with `y`. -/
noncomputable def curryValueMap
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H)
    {S : C} (p : S ⟶ U) (x : F.obj (op S)) {T : C} (q : T ⟶ S) :
    G.obj (op T) →ₗ[O.obj (op T)] H.obj (op T) :=
  (restrTensorHom O F G H U a (q ≫ p)).comp
    (TensorProduct.mk (O.obj (op T)) (F.obj (op T)) (G.obj (op T)) (F.restrictₛₗ q.op x))

/-- Unfolding `curryValueMap`: it evaluates `a` on the restriction of `x` tensored with `y`. -/
theorem curryValueMap_apply
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H)
    {S : C} (p : S ⟶ U) (x : F.obj (op S)) {T : C} (q : T ⟶ S) (y : G.obj (op T)) :
    curryValueMap O F G H U a p x q y =
      restrTensorHom O F G H U a (q ≫ p) (F.restrictₛₗ q.op x ⊗ₜ y) := rfl

/-- `curryValueMap` is additive in the section of `F`. -/
theorem curryValueMap_add_left
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H)
    {S : C} (p : S ⟶ U) (x x' : F.obj (op S)) {T : C} (q : T ⟶ S) (y : G.obj (op T)) :
    curryValueMap O F G H U a p (x + x') q y =
      curryValueMap O F G H U a p x q y + curryValueMap O F G H U a p x' q y := by
  rw [curryValueMap_apply, curryValueMap_apply, curryValueMap_apply, map_add,
    TensorProduct.add_tmul, map_add]

/-- `curryValueMap` is semilinear in the section of `F`. -/
theorem curryValueMap_smul_left
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H)
    {S : C} (p : S ⟶ U) (r : O.obj (op S)) (x : F.obj (op S)) {T : C} (q : T ⟶ S)
    (y : G.obj (op T)) :
    curryValueMap O F G H U a p (r • x) q y =
      (O.map q.op).hom r • curryValueMap O F G H U a p x q y := by
  rw [curryValueMap_apply, curryValueMap_apply, restrictₛₗ_smul,
    ← TensorProduct.smul_tmul', map_smul]

/-- `curryValueMap` is compatible with restriction in the second slice. -/
theorem curryValueMap_restrict
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H)
    {S : C} (p : S ⟶ U) (x : F.obj (op S)) {T T' : C} (q : T ⟶ S) (k : T' ⟶ T)
    (y : G.obj (op T)) :
    curryValueMap O F G H U a p x (k ≫ q) (G.restrictₛₗ k.op y) =
      H.restrictₛₗ k.op (curryValueMap O F G H U a p x q y) := by
  rw [curryValueMap_apply, curryValueMap_apply, Category.assoc, op_comp,
    restrictₛₗ_comp_apply]
  exact restrTensorHom_nat O F G H U a (q ≫ p) k (F.restrictₛₗ q.op x) y

/-- Currying of `a` at a section `x` of `F` over `p : S ⟶ U`: a morphism `G|_S ⟶ H|_S`. -/
noncomputable def currySectionValue
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H)
    {S : C} (p : S ⟶ U) (x : F.obj (op S)) :
    (restrFun O S).obj G ⟶ (restrFun O S).obj H :=
  _root_.PresheafOfModules.Hom.mk
    (fun Y ↦ ofRestrHom O G H S Y (curryValueMap O F G H U a p x Y.unop.hom))
    (fun {Y Z} f ↦ by
      refine ModuleCat.hom_ext (LinearMap.ext fun y ↦ ?_)
      have h := curryValueMap_restrict O F G H U a p x Y.unop.hom f.unop.left y
      rw [Over.w f.unop] at h
      exact h)

/-- Currying on sections over `p : S ⟶ U`, as an `O(S)`-linear map into the internal Hom. -/
noncomputable def currySectionMap
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H) {S : C} (p : S ⟶ U) :
    F.obj (op S) →ₗ[O.obj (op S)] (internalHom O G H).obj (op S) where
  toFun x := currySectionValue O F G H U a p x
  map_add' x x' := _root_.PresheafOfModules.hom_ext fun Y ↦ ModuleCat.hom_ext <|
    LinearMap.ext fun y ↦ curryValueMap_add_left O F G H U a p x x' Y.unop.hom y
  map_smul' r x := _root_.PresheafOfModules.hom_ext fun Y ↦ ModuleCat.hom_ext <|
    LinearMap.ext fun y ↦ curryValueMap_smul_left O F G H U a p r x Y.unop.hom y

/-- Restricting an internal-Hom section re-indexes the slice. -/
theorem homRestr_section {T S : C} (k : T ⟶ S)
    (α : (restrFun O S).obj G ⟶ (restrFun O S).obj H) {W : C} (q : W ⟶ T)
    (w : G.obj (op W)) :
    sectionOfRestr O H T q
        (((homRestr O G H k α).app (op (Over.mk q))).hom (restrSection O G T q w)) =
      sectionOfRestr O H S (q ≫ k)
        ((α.app (op (Over.mk (q ≫ k)))).hom (restrSection O G S (q ≫ k) w)) := rfl

/-- Restricting the base of `curryValueMap` reindexes the slice. -/
theorem curryValueMap_base_restrict
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H)
    {S S' : C} (p : S ⟶ U) (k : S' ⟶ S) (x : F.obj (op S)) {T : C} (q : T ⟶ S')
    (y : G.obj (op T)) :
    curryValueMap O F G H U a (k ≫ p) (F.restrictₛₗ k.op x) q y =
      curryValueMap O F G H U a p x (q ≫ k) y := by
  rw [curryValueMap_apply, curryValueMap_apply, Category.assoc, op_comp,
    restrictₛₗ_comp_apply]

/-- Restricting the base of `currySectionValue` is restriction of internal-Hom sections. -/
theorem currySectionValue_base_restrict
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H)
    {S S' : C} (p : S ⟶ U) (k : S' ⟶ S) (x : F.obj (op S)) :
    currySectionValue O F G H U a (k ≫ p) (F.restrictₛₗ k.op x) =
      homRestr O G H k (currySectionValue O F G H U a p x) :=
  _root_.PresheafOfModules.hom_ext fun W ↦ ModuleCat.hom_ext <|
    LinearMap.ext fun w ↦ curryValueMap_base_restrict O F G H U a p k x W.unop.hom w

/-- Currying on sections over `U`: a morphism `(F ⊗ G)|_U ⟶ H|_U` becomes a morphism
`F|_U ⟶ Hom_O(G, H)|_U`. -/
noncomputable def currySection
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H) :
    (restrFun O U).obj F ⟶ (restrFun O U).obj (internalHom O G H) :=
  _root_.PresheafOfModules.Hom.mk
    (fun X ↦ ofRestrHom O F (internalHom O G H) U X
      (currySectionMap O F G H U a X.unop.hom))
    (fun {X X'} f ↦ by
      refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
      have h := currySectionValue_base_restrict O F G H U a X.unop.hom f.unop.left x
      rw [Over.w f.unop] at h
      exact h)

/-- Applying a morphism into the internal Hom presheaf at a section over `p : S ⟶ U`, as an
`O(S)`-linear map. -/
noncomputable def restrHomApplyLinear
    (b : (restrFun O U).obj F ⟶ (restrFun O U).obj (internalHom O G H))
    {S : C} (p : S ⟶ U) :
    F.obj (op S) →ₗ[O.obj (op S)] internalHomObj O G H S :=
  (b.app (op (Over.mk p))).hom

/-- Evaluating an internal-Hom section at the identity of its slice, as an `O(S)`-linear
map. -/
noncomputable def evalAtIdLinear (S : C) :
    internalHomObj O G H S →ₗ[O.obj (op S)]
      (G.obj (op S) →ₗ[O.obj (op S)] H.obj (op S)) where
  toFun α := (α.app (op (Over.mk (𝟙 S)))).hom
  map_add' _ _ := rfl
  map_smul' r α := by
    apply LinearMap.ext
    intro y
    change (((α ≫ multEndoHom O H S r).app (op (Over.mk (𝟙 S)))).hom
      (restrSection O G S (𝟙 S) y) : H.obj (op S)) = _
    change fRestr O S r (op (Over.mk (𝟙 S))) •
      ((α.app (op (Over.mk (𝟙 S)))).hom (restrSection O G S (𝟙 S) y) : H.obj (op S)) = _
    have hr : fRestr O S r (op (Over.mk (𝟙 S))) = r := by
      change ((Oforget O).map (𝟙 (op S))).hom r = r
      rw [CategoryTheory.Functor.map_id]
      rfl
    rw [hr]
    rfl

/-- The uncurried map, bilinear by construction. -/
noncomputable def uncurryBilin
    (b : (restrFun O U).obj F ⟶ (restrFun O U).obj (internalHom O G H))
    {S : C} (p : S ⟶ U) :
    F.obj (op S) →ₗ[O.obj (op S)] G.obj (op S) →ₗ[O.obj (op S)] H.obj (op S) :=
  (evalAtIdLinear O G H S).comp (restrHomApplyLinear O F G H U b p)

/-- The uncurried map on the tensor product of plain sections. -/
noncomputable def uncurryTensorMap
    (b : (restrFun O U).obj F ⟶ (restrFun O U).obj (internalHom O G H))
    {S : C} (p : S ⟶ U) :
    TensorProduct (O.obj (op S)) (F.obj (op S)) (G.obj (op S)) →ₗ[O.obj (op S)]
      H.obj (op S) :=
  TensorProduct.lift (uncurryBilin O F G H U b p)

/-- Unfolding `uncurryTensorMap` on a pure tensor: evaluate at the identity of the slice. -/
theorem uncurryTensorMap_tmul
    (b : (restrFun O U).obj F ⟶ (restrFun O U).obj (internalHom O G H))
    {S : C} (p : S ⟶ U) (x : F.obj (op S)) (y : G.obj (op S)) :
    uncurryTensorMap O F G H U b p (x ⊗ₜ y) =
      sectionOfRestr O H S (𝟙 S)
        ((((b.app (op (Over.mk p))).hom (restrSection O F U p x)).app
          (op (Over.mk (𝟙 S)))).hom (restrSection O G S (𝟙 S) y)) := rfl

/-- A pure tensor of plain sections, as a section of `(F ⊗ G)|_U` over a general object. -/
noncomputable def restrTmulAt (X : (Over U)ᵒᵖ)
    (x : F.obj (op X.unop.left)) (y : G.obj (op X.unop.left)) :
    ((restrFun O U).obj (F ⊗ G)).obj X :=
  x ⊗ₜ[O.obj (op X.unop.left)] y

/-- Two morphisms out of a restricted tensor product agree as soon as they agree on the pure
tensors of plain sections. -/
theorem restrTensor_hom_ext {X : (Over U)ᵒᵖ} {Z : ModuleCat ((ORestr O U).obj X)}
    {φ ψ : ((restrFun O U).obj (F ⊗ G)).obj X ⟶ Z}
    (h : ∀ (x : F.obj (op X.unop.left)) (y : G.obj (op X.unop.left)),
      φ.hom (restrTmulAt O F G U X x y) = ψ.hom (restrTmulAt O F G U X x y)) :
    φ = ψ := by
  refine ModuleCat.hom_ext (LinearMap.ext fun t ↦ ?_)
  induction t using TensorProduct.induction_on with
  | zero => exact (map_zero φ.hom).trans (map_zero ψ.hom).symm
  | tmul x y => exact h x y
  | add t t' ht ht' =>
      have hsum : φ.hom t + φ.hom t' = ψ.hom t + ψ.hom t' := by rw [ht, ht']
      exact (map_add φ.hom t t').trans (hsum.trans (map_add ψ.hom t t').symm)

/-- Naturality of a slice-level morphism `G|_S ⟶ H|_S`, on plain sections. -/
theorem restrMorphism_nat {S : C} (α : (restrFun O S).obj G ⟶ (restrFun O S).obj H)
    {T T' : C} (q : T ⟶ S) (k : T' ⟶ T) (y : G.obj (op T)) :
    sectionOfRestr O H S (k ≫ q)
        ((α.app (op (Over.mk (k ≫ q)))).hom
          (restrSection O G S (k ≫ q) (G.restrictₛₗ k.op y))) =
      H.restrictₛₗ k.op
        (sectionOfRestr O H S q ((α.app (op (Over.mk q))).hom (restrSection O G S q y))) :=
  congrArg (sectionOfRestr O H S (k ≫ q))
    (_root_.PresheafOfModules.naturality_apply α
      ((Over.homMk k : (Over.mk (k ≫ q) : Over S) ⟶ Over.mk q).op)
      (restrSection O G S q y))

/-- Naturality of a morphism into the internal Hom presheaf, on plain sections. -/
theorem restrHomApplyLinear_nat
    (b : (restrFun O U).obj F ⟶ (restrFun O U).obj (internalHom O G H))
    {S S' : C} (p : S ⟶ U) (k : S' ⟶ S) (x : F.obj (op S)) :
    restrHomApplyLinear O F G H U b (k ≫ p) (F.restrictₛₗ k.op x) =
      homRestr O G H k (restrHomApplyLinear O F G H U b p x) :=
  congrArg (sectionOfRestr O (internalHom O G H) U (k ≫ p))
    (_root_.PresheafOfModules.naturality_apply b
      ((Over.homMk k : (Over.mk (k ≫ p) : Over U) ⟶ Over.mk p).op)
      (restrSection O F U p x))

/-- `uncurryTensorMap` on a restricted section and a plain section is the value of the curried
section on the plain section. -/
private theorem uncurryTensorMap_restrict_tmul
    (b : (restrFun O U).obj F ⟶ (restrFun O U).obj (internalHom O G H))
    {S S' : C} (p : S ⟶ U) (k : S' ⟶ S) (x : F.obj (op S)) (y : G.obj (op S')) :
    uncurryTensorMap O F G H U b (k ≫ p) (F.restrictₛₗ k.op x ⊗ₜ y) =
      sectionOfRestr O H S k
        (((restrHomApplyLinear O F G H U b p x).app (op (Over.mk k))).hom
          (restrSection O G S k y)) := by
  have hr := homRestr_section O G H k (restrHomApplyLinear O F G H U b p x) (𝟙 S') y
  rw [Category.id_comp] at hr
  rw [uncurryTensorMap_tmul]
  show sectionOfRestr O H S' (𝟙 S')
      (((restrHomApplyLinear O F G H U b (k ≫ p) (F.restrictₛₗ k.op x)).app
        (op (Over.mk (𝟙 S')))).hom (restrSection O G S' (𝟙 S') y)) = _
  rw [restrHomApplyLinear_nat]
  exact hr

/-- `uncurryTensorMap` is compatible with restriction. -/
theorem uncurryTensorMap_restrict
    (b : (restrFun O U).obj F ⟶ (restrFun O U).obj (internalHom O G H))
    {S S' : C} (p : S ⟶ U) (k : S' ⟶ S) (x : F.obj (op S)) (y : G.obj (op S)) :
    uncurryTensorMap O F G H U b (k ≫ p)
        (F.restrictₛₗ k.op x ⊗ₜ G.restrictₛₗ k.op y) =
      H.restrictₛₗ k.op (uncurryTensorMap O F G H U b p (x ⊗ₜ y)) := by
  have hα := restrMorphism_nat O G H (restrHomApplyLinear O F G H U b p x) (𝟙 S) k y
  rw [Category.comp_id] at hα
  rw [uncurryTensorMap_restrict_tmul, uncurryTensorMap_tmul]
  exact hα

/-- Uncurrying on sections over `U`, inverse to `currySection`. -/
noncomputable def uncurrySection
    (b : (restrFun O U).obj F ⟶ (restrFun O U).obj (internalHom O G H)) :
    (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H :=
  _root_.PresheafOfModules.Hom.mk
    (fun X ↦ ofRestrHom O (F ⊗ G) H U X (uncurryTensorMap O F G H U b X.unop.hom))
    (fun {X Z} f ↦ by
      refine restrTensor_hom_ext O F G U ?_
      intro x y
      have hw : f.unop.left ≫ X.unop.hom = Z.unop.hom := Over.w f.unop
      change uncurryTensorMap O F G H U b Z.unop.hom
          (F.restrictₛₗ f.unop.left.op x ⊗ₜ G.restrictₛₗ f.unop.left.op y) =
        H.restrictₛₗ f.unop.left.op
          (uncurryTensorMap O F G H U b X.unop.hom (x ⊗ₜ y))
      rw [← hw]
      exact uncurryTensorMap_restrict O F G H U b X.unop.hom f.unop.left x y)

/-- Restriction along an identity is the identity. -/
theorem restrictₛₗ_id (M : _root_.PresheafOfModules.{max u v w} (Oforget O)) {X : Cᵒᵖ}
    (x : M.obj X) :
    M.restrictₛₗ (𝟙 X) x = x := by
  simp only [_root_.PresheafOfModules.restrictₛₗ_apply]
  exact congrFun (congrArg (fun f ↦ (ModuleCat.Hom.hom f).toFun) (M.map_id X)) x

/-- Uncurrying undoes currying. -/
theorem uncurrySection_currySection
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H) :
    uncurrySection O F G H U (currySection O F G H U a) = a := by
  apply _root_.PresheafOfModules.hom_ext
  intro X
  refine restrTensor_hom_ext O F G U ?_
  intro x y
  show uncurryTensorMap O F G H U (currySection O F G H U a) X.unop.hom (x ⊗ₜ y) =
    restrTensorHom O F G H U a X.unop.hom (x ⊗ₜ y)
  rw [uncurryTensorMap_tmul]
  show curryValueMap O F G H U a X.unop.hom x (𝟙 X.unop.left) y = _
  rw [curryValueMap_apply, Category.id_comp, op_id, restrictₛₗ_id]

/-- Two morphisms `F|_U ⟶ Hom_O(G, H)|_U` are equal as soon as, for every plain section `x` of
`F` over `p : S ⟶ U`, their values agree on every plain section `y` of `G` over `q : T ⟶ S`: a
section of the internal Hom is determined by its values on plain sections. -/
theorem restrInternalHom_hom_ext
    {φ ψ : (restrFun O U).obj F ⟶ (restrFun O U).obj (internalHom O G H)}
    (h : ∀ {S : C} (p : S ⟶ U) (x : F.obj (op S)) {T : C} (q : T ⟶ S) (y : G.obj (op T)),
      sectionOfRestr O H S q
          (((restrHomApplyLinear O F G H U φ p x).app (op (Over.mk q))).hom
            (restrSection O G S q y)) =
        sectionOfRestr O H S q
          (((restrHomApplyLinear O F G H U ψ p x).app (op (Over.mk q))).hom
            (restrSection O G S q y))) :
    φ = ψ :=
  _root_.PresheafOfModules.hom_ext fun X ↦ ModuleCat.hom_ext <| LinearMap.ext fun x ↦
    _root_.PresheafOfModules.hom_ext fun Y ↦ ModuleCat.hom_ext <| LinearMap.ext fun y ↦
      h X.unop.hom x Y.unop.hom y

/-- Currying an uncurried morphism recovers its values on sections. -/
theorem curryValueMap_uncurrySection
    (b : (restrFun O U).obj F ⟶ (restrFun O U).obj (internalHom O G H))
    {S : C} (p : S ⟶ U) (x : F.obj (op S)) {T : C} (q : T ⟶ S) (y : G.obj (op T)) :
    curryValueMap O F G H U (uncurrySection O F G H U b) p x q y =
      sectionOfRestr O H S q
        (((restrHomApplyLinear O F G H U b p x).app (op (Over.mk q))).hom
          (restrSection O G S q y)) := by
  rw [curryValueMap_apply]
  exact uncurryTensorMap_restrict_tmul O F G H U b p q x y

/-- Currying undoes uncurrying. -/
theorem currySection_uncurrySection
    (b : (restrFun O U).obj F ⟶ (restrFun O U).obj (internalHom O G H)) :
    currySection O F G H U (uncurrySection O F G H U b) = b :=
  restrInternalHom_hom_ext O F G H U fun {_} p x {_} q y ↦
    curryValueMap_uncurrySection O F G H U b p x q y

/-- `curryValueMap` is additive in the morphism being curried. -/
theorem curryValueMap_add_hom (a a' : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H)
    {S : C} (p : S ⟶ U) (x : F.obj (op S)) {T : C} (q : T ⟶ S) (y : G.obj (op T)) :
    curryValueMap O F G H U (a + a') p x q y =
      curryValueMap O F G H U a p x q y + curryValueMap O F G H U a' p x q y := rfl

/-- `curryValueMap` is semilinear in the morphism being curried. -/
theorem curryValueMap_smul_hom (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H)
    (r : O.obj (op U)) {S : C} (p : S ⟶ U) (x : F.obj (op S)) {T : C} (q : T ⟶ S)
    (y : G.obj (op T)) :
    curryValueMap O F G H U (smulHom O (F ⊗ G) H U r a) p x q y =
      (O.map q.op).hom ((O.map p.op).hom r) • curryValueMap O F G H U a p x q y := by
  have h : (O.map (q ≫ p).op).hom r = (O.map q.op).hom ((O.map p.op).hom r) := by
    rw [op_comp, CategoryTheory.Functor.map_comp]
    rfl
  rw [← h]
  rfl

/-- Currying on sections over `U` is additive. -/
theorem currySection_add (a a' : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H) :
    currySection O F G H U (a + a') =
      currySection O F G H U a + currySection O F G H U a' :=
  restrInternalHom_hom_ext O F G H U fun {_} p x {_} q y ↦
    curryValueMap_add_hom O F G H U a a' p x q y

/-- Currying on sections over `U` is `O(U)`-linear. -/
theorem currySection_smul (r : O.obj (op U))
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H) :
    currySection O F G H U (smulHom O (F ⊗ G) H U r a) =
      smulHom O F (internalHom O G H) U r (currySection O F G H U a) :=
  restrInternalHom_hom_ext O F G H U fun {_} p x {_} q y ↦
    curryValueMap_smul_hom O F G H U a r p x q y

/-- Currying on sections over `U`, as an `O(U)`-linear map of internal Hom modules. -/
noncomputable def currySectionLinearMap :
    internalHomObj O (F ⊗ G) H U →ₗ[O.obj (op U)]
      internalHomObj O F (internalHom O G H) U where
  toFun := currySection O F G H U
  map_add' := currySection_add O F G H U
  map_smul' := currySection_smul O F G H U

/-- Currying on sections over `U` is bijective, `uncurrySection` being a two-sided inverse. -/
theorem currySectionLinearMap_bijective :
    Function.Bijective (currySectionLinearMap O F G H U) :=
  Function.bijective_iff_has_inverse.mpr ⟨uncurrySection O F G H U,
    uncurrySection_currySection O F G H U, currySection_uncurrySection O F G H U⟩

/-- Restricting the base of a slice-level morphism reindexes it. -/
theorem restrTensorHom_homRestr (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H)
    {U' : C} (k : U' ⟶ U) {W : C} (h : W ⟶ U') (x : F.obj (op W)) (y : G.obj (op W)) :
    restrTensorHom O F G H U' (homRestr O (F ⊗ G) H k a) h (x ⊗ₜ y) =
      restrTensorHom O F G H U a (h ≫ k) (x ⊗ₜ y) := rfl

/-- `curryValueMap` commutes with restriction of the base. -/
theorem curryValueMap_homRestr (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H)
    {U' : C} (k : U' ⟶ U) {S : C} (p : S ⟶ U') (x : F.obj (op S)) {T : C} (q : T ⟶ S)
    (y : G.obj (op T)) :
    curryValueMap O F G H U' (homRestr O (F ⊗ G) H k a) p x q y =
      curryValueMap O F G H U a (p ≫ k) x q y := by
  rw [curryValueMap_apply, curryValueMap_apply, restrTensorHom_homRestr, Category.assoc]

/-- Currying commutes with restriction of the base of the morphism being curried. -/
theorem currySectionValue_homRestr
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H)
    {U' : C} (k : U' ⟶ U) {S : C} (p : S ⟶ U') (x : F.obj (op S)) :
    currySectionValue O F G H U' (homRestr O (F ⊗ G) H k a) p x =
      currySectionValue O F G H U a (p ≫ k) x :=
  _root_.PresheafOfModules.hom_ext fun Y ↦ ModuleCat.hom_ext <|
    LinearMap.ext fun y ↦ curryValueMap_homRestr O F G H U a k p x Y.unop.hom y

/-- Generic: applying a re-indexed internal-Hom section. -/
theorem homRestr_app_apply (M N : _root_.PresheafOfModules.{max u v w} (Oforget O))
    {T S : C} (k : T ⟶ S) (φ : (restrFun O S).obj M ⟶ (restrFun O S).obj N)
    (V : (Over T)ᵒᵖ) (w : ((restrFun O T).obj M).obj V) :
    ((homRestr O M N k φ).app V).hom w =
      (φ.app (op (Over.mk (V.unop.hom ≫ k)))).hom w := rfl

/-- Currying commutes with the restriction maps of the internal Hom presheaf: this is the
naturality of the currying isomorphism. -/
theorem currySection_homRestr
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H) {U' : C} (k : U' ⟶ U) :
    currySection O F G H U' (homRestr O (F ⊗ G) H k a) =
      homRestr O F (internalHom O G H) k (currySection O F G H U a) := by
  refine _root_.PresheafOfModules.hom_ext fun X ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  rw [homRestr_app_apply O F (internalHom O G H) k (currySection O F G H U a) X x]
  exact currySectionValue_homRestr O F G H U a k X.unop.hom x

/-- **Stacks 03EO.** The canonical currying isomorphism from internal Hom out of a tensor
product to iterated internal Hom. -/
@[stacks 03EO "presheaf_internal_hom_tensor_iso"]
noncomputable def presheafInternalHomTensorIso :
    internalHom O (F ⊗ G) H ≅ internalHom O F (internalHom O G H) :=
  _root_.PresheafOfModules.isoMk
    (fun X ↦ (LinearEquiv.ofBijective (currySectionLinearMap O F G H X.unop)
      (currySectionLinearMap_bijective O F G H X.unop)).toModuleIso)
    (fun {X V} f ↦ by
      refine ModuleCat.hom_ext (LinearMap.ext fun a ↦ ?_)
      exact currySection_homRestr O F G H X.unop a f.unop)

/-- On sections, the currying isomorphism is tensor currying: after restricting `x`, it
evaluates the original morphism on `x ⊗ y`. This pins the isomorphism down, rather than merely
asserting that some isomorphism exists. -/
@[stacks 03EO "presheaf_internal_hom_tensor_iso"]
theorem presheafInternalHomTensorIso_hom_app (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H)
    {S : C} (p : S ⟶ U) (x : F.obj (op S)) {T : C} (q : T ⟶ S) (y : G.obj (op T)) :
    sectionOfRestr O H S q
        (((((((presheafInternalHomTensorIso O F G H).hom.app (op U)).hom a).app
            (op (Over.mk p))).hom (restrSection O F U p x)).app
              (op (Over.mk q))).hom (restrSection O G S q y)) =
      restrTensorHom O F G H U a (q ≫ p) (F.restrictₛₗ q.op x ⊗ₜ y) := rfl

/-- Precomposing with `f ⊗ₘ 𝟙` applies `f` to the left tensor factor. -/
theorem restrTensorHom_mapLeft {F' : _root_.PresheafOfModules.{max u v w} (Oforget O)}
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H) (f : F' ⟶ F)
    {W : C} (h : W ⟶ U) (x : F'.obj (op W)) (y : G.obj (op W)) :
    restrTensorHom O F' G H U ((restrFun O U).map (f ⊗ₘ 𝟙 G) ≫ a) h (x ⊗ₜ y) =
      restrTensorHom O F G H U a h (f.app (op W) x ⊗ₜ y) := rfl

/-- Precomposing with `𝟙 ⊗ₘ g` applies `g` to the right tensor factor. -/
theorem restrTensorHom_mapMiddle {G' : _root_.PresheafOfModules.{max u v w} (Oforget O)}
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H) (g : G' ⟶ G)
    {W : C} (h : W ⟶ U) (x : F.obj (op W)) (y : G'.obj (op W)) :
    restrTensorHom O F G' H U ((restrFun O U).map (𝟙 F ⊗ₘ g) ≫ a) h (x ⊗ₜ y) =
      restrTensorHom O F G H U a h (x ⊗ₜ g.app (op W) y) := rfl

/-- Postcomposing applies the morphism to the value. -/
theorem restrTensorHom_postcomp
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H)
    {H' : _root_.PresheafOfModules.{max u v w} (Oforget O)} (hh : H ⟶ H')
    {W : C} (h : W ⟶ U) (x : F.obj (op W)) (y : G.obj (op W)) :
    restrTensorHom O F G H' U (a ≫ (restrFun O U).map hh) h (x ⊗ₜ y) =
      hh.app (op W) (restrTensorHom O F G H U a h (x ⊗ₜ y)) := rfl

/-- Naturality of a morphism of presheaves of modules, in terms of `restrictₛₗ`. -/
theorem naturality_restrictₛₗ {M₁ M₂ : _root_.PresheafOfModules.{max u v w} (Oforget O)}
    (f : M₁ ⟶ M₂) {X Y : Cᵒᵖ} (g : X ⟶ Y) (x : M₁.obj X) :
    f.app Y (M₁.restrictₛₗ g x) = M₂.restrictₛₗ g (f.app X x) :=
  _root_.PresheafOfModules.naturality_apply f g x

/-- Two morphisms into an iterated internal Hom `Hom_O(P, Hom_O(Q, R))` are equal as soon as all
their values agree: on a section `a` over `X`, a plain section `x` of `P` over `p : S ⟶ X`, and a
plain section `y` of `Q` over `q : T ⟶ S`. -/
theorem iteratedInternalHom_hom_ext
    {K P Q R : _root_.PresheafOfModules.{max u v w} (Oforget O)}
    {Φ Ψ : K ⟶ internalHom O P (internalHom O Q R)}
    (h : ∀ (X : Cᵒᵖ) (a : K.obj X) {S : C} (p : S ⟶ X.unop) (x : P.obj (op S)) {T : C}
        (q : T ⟶ S) (y : Q.obj (op T)),
      sectionOfRestr O R S q
          (((restrHomApplyLinear O P Q R X.unop ((Φ.app X).hom a) p x).app
            (op (Over.mk q))).hom (restrSection O Q S q y)) =
        sectionOfRestr O R S q
          (((restrHomApplyLinear O P Q R X.unop ((Ψ.app X).hom a) p x).app
            (op (Over.mk q))).hom (restrSection O Q S q y))) :
    Φ = Ψ :=
  _root_.PresheafOfModules.hom_ext fun X ↦ ModuleCat.hom_ext <| LinearMap.ext fun a ↦
    restrInternalHom_hom_ext O P Q R X.unop fun {_} p x {_} q y ↦ h X a p x q y

/-- Currying is contravariantly functorial in the first tensor factor. -/
theorem curryValueMap_mapLeft {F' : _root_.PresheafOfModules.{max u v w} (Oforget O)}
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H) (f : F' ⟶ F)
    {S : C} (p : S ⟶ U) (x : F'.obj (op S)) {T : C} (q : T ⟶ S) (y : G.obj (op T)) :
    curryValueMap O F G H U a p (f.app (op S) x) q y =
      curryValueMap O F' G H U ((restrFun O U).map (f ⊗ₘ 𝟙 G) ≫ a) p x q y := by
  rw [curryValueMap_apply, curryValueMap_apply, restrTensorHom_mapLeft,
    naturality_restrictₛₗ]

/-- **Stacks 03EO.** The currying isomorphism is natural contravariantly in its first tensor
factor. -/
@[stacks 03EO "presheaf_internal_hom_tensor_iso"]
theorem presheafInternalHomTensorIso_natural_left
    {F' : _root_.PresheafOfModules.{max u v w} (Oforget O)} (f : F' ⟶ F) :
    (presheafInternalHomTensorIso O F G H).hom ≫
        internalHomMapLeft O f =
      internalHomMapLeft O (f ⊗ₘ 𝟙 G) ≫
        (presheafInternalHomTensorIso O F' G H).hom :=
  iteratedInternalHom_hom_ext O fun X a {_} p x {_} q y ↦
    curryValueMap_mapLeft O F G H X.unop a f p x q y

/-- Currying is contravariantly functorial in the second tensor factor. -/
theorem curryValueMap_mapMiddle {G' : _root_.PresheafOfModules.{max u v w} (Oforget O)}
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H) (g : G' ⟶ G)
    {S : C} (p : S ⟶ U) (x : F.obj (op S)) {T : C} (q : T ⟶ S) (y : G'.obj (op T)) :
    curryValueMap O F G H U a p x q (g.app (op T) y) =
      curryValueMap O F G' H U ((restrFun O U).map (𝟙 F ⊗ₘ g) ≫ a) p x q y := by
  rw [curryValueMap_apply, curryValueMap_apply, restrTensorHom_mapMiddle]

/-- Currying is covariantly functorial in the target. -/
theorem curryValueMap_postcomp
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H)
    {H' : _root_.PresheafOfModules.{max u v w} (Oforget O)} (hh : H ⟶ H')
    {S : C} (p : S ⟶ U) (x : F.obj (op S)) {T : C} (q : T ⟶ S) (y : G.obj (op T)) :
    curryValueMap O F G H' U (a ≫ (restrFun O U).map hh) p x q y =
      hh.app (op T) (curryValueMap O F G H U a p x q y) := by
  rw [curryValueMap_apply, curryValueMap_apply, restrTensorHom_postcomp]

/-- **Stacks 03EO.** The currying isomorphism is natural contravariantly in its second tensor
factor. -/
@[stacks 03EO "presheaf_internal_hom_tensor_iso"]
theorem presheafInternalHomTensorIso_natural_middle
    {G' : _root_.PresheafOfModules.{max u v w} (Oforget O)} (g : G' ⟶ G) :
    (presheafInternalHomTensorIso O F G H).hom ≫
        internalHomMapRight O F
          (internalHomMapLeft O g) =
      internalHomMapLeft O (𝟙 F ⊗ₘ g) ≫
        (presheafInternalHomTensorIso O F G' H).hom :=
  iteratedInternalHom_hom_ext O fun X a {_} p x {_} q y ↦
    curryValueMap_mapMiddle O F G H X.unop a g p x q y

/-- **Stacks 03EO.** The currying isomorphism is natural covariantly in its target. -/
@[stacks 03EO "presheaf_internal_hom_tensor_iso"]
theorem presheafInternalHomTensorIso_natural_right
    {H' : _root_.PresheafOfModules.{max u v w} (Oforget O)} (hh : H ⟶ H') :
    internalHomMapRight O (F ⊗ G) hh ≫
        (presheafInternalHomTensorIso O F G H').hom =
      (presheafInternalHomTensorIso O F G H).hom ≫
        internalHomMapRight O F
          (internalHomMapRight O G hh) :=
  iteratedInternalHom_hom_ext O fun X a {_} p x {_} q y ↦
    curryValueMap_postcomp O F G H X.unop a hh p x q y

end Stacks.PresheafOfModules.InternalHom

end
