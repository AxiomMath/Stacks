module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHom
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower

/-!
# An invertible tensor factor identifies the other factor with an internal Hom

Let `𝒪` be a presheaf of commutative rings on a site `(C, J)` whose underlying presheaf of
rings is a sheaf, let `G` be an invertible sheaf of `𝒪`-modules and let `M`, `H` be sheaves of
`𝒪`-modules together with an isomorphism `M ⊗_𝒪 G ≅ H`.  Then `M` is the internal Hom
`Hom_𝒪(G, H)`: a section of `M` over an object `U` of the site is the same thing as a morphism
`G|_U ⟶ H|_U` on the slice site over `U`.

The comparison is the usual currying.  A section `s` of `M` over `U` goes to the morphism which
takes a section `t` of `G` over an object of `C/U` to the value of the pairing `M ⊗_𝒪 G ⟶ H` on
`s ⊗ t`.

## Main definitions

* `Stacks.PresheafOfModules.TensorInternalHom.homSection` and `homSectionLinearMap`: the
  currying map, for a morphism `b : F ⊗ G ⟶ H` of presheaves of modules and a section of `F`.
* `Stacks.PresheafOfModules.TensorInternalHom.freeRepresentable` is the free presheaf of
  modules on a representable presheaf of sets, and
  `Stacks.PresheafOfModules.TensorInternalHom.tensorFreeHomEquiv` identifies the morphisms
  `free(U) ⊗ G ⟶ H` with the sections of `Hom_𝒪(G, H)` over `U`.
* `Stacks.SheafOfModules.Invertible.tensorCurryLinearEquiv` is the comparison
  `M(U) ≃ Hom_𝒪(G, H)(U)` attached to an invertible `G` and an isomorphism `M ⊗_𝒪 G ≅ H`.

## Main results

* `Stacks.SheafOfModules.Invertible.tensorHom_bijective_of_isInvertible`: for invertible `G`,
  precomposing with the pairing `M ⊗ G ⟶ H` is a bijection from the morphisms of presheaves of
  modules `A ⟶ M` onto the morphisms `A ⊗ G ⟶ H`.
* `Stacks.SheafOfModules.Invertible.tensorCurryLinearEquiv_natural`: the comparison commutes
  with the restriction maps.
* `Stacks.SheafOfModules.Invertible.tensorCurryLinearEquiv_apply`: the comparison is pinned
  down by the pairing — the morphism attached to a section `s` takes `t` to the value of the
  pairing on `s ⊗ t`.

## Implementation notes

**Universes.** The module universe `w` is both the universe of the rings of sections and the
universe of the morphisms of the site: the first because the monoidal structure on presheaves
of modules requires it, the second because the free module on a representable presheaf of sets
is only defined then.  The universe of the objects of the site is free, and this matters:
`Hom_𝒪(G, H)` has its sections in `max u w`, one universe above the sections of `G` and `H`
when the objects of the site live above its morphisms, as they do on the small étale site of an
algebraic space.  So the comparison cannot be an isomorphism of sheaves of modules, and is
instead a family of linear equivalences on sections, natural for restriction.  For the same
reason the currying isomorphism
`Stacks.PresheafOfModules.InternalHom.presheafInternalHomTensorIso` does not apply here: it is an
isomorphism of presheaves of modules, so it needs the sections of the internal Hom to lie in the
module universe, which forces `w = max u w`.

**Retyping.** A section of `M|_U` over an object `V` of `C/U`, a section of `M` over the object
underlying `V`, and the value of a semilinear restriction map all have the same carrier but
carry different `ModuleCat` indices, and instance search cannot connect the spellings.  Rather
than relax the ambient transparency, each identification is named once — `restrSection`,
`sectionOfRestr` and `ofRestrHom` — and the development is phrased through those names.

## References

* [Stacks Project, Tag 0841](https://stacks.math.columbia.edu/tag/0841)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite
open scoped TensorProduct

universe u w

namespace Stacks.PresheafOfModules.TensorInternalHom

variable {C : Type u} [Category.{w} C] (O : Cᵒᵖ ⥤ CommRingCat.{w})

attribute [local instance] _root_.PresheafOfModulesOfCommRing.monoidalCategory

/-! ### Retyping the sections of a restriction -/

section Retyping

variable (M N : _root_.PresheafOfModules.{w} (Oforget O))

/-- A section of `M` over the object underlying `V`, read as a section of `M|_U` over `V`. -/
def restrSection (U : C) (V : (Over U)ᵒᵖ) (x : M.obj (op V.unop.left)) :
    ((restrFun O U).obj M).obj V := x

/-- A section of `M|_U` over `V`, read as a section of `M` over the object underlying `V`. -/
def sectionOfRestr (U : C) (V : (Over U)ᵒᵖ) (x : ((restrFun O U).obj M).obj V) :
    M.obj (op V.unop.left) := x

/-- A linear map of the plain sections over the object underlying `V`, read as a map of the
sections of the restrictions to the slice site. -/
def ofRestrHom (U : C) (V : (Over U)ᵒᵖ)
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

/-- A section of the internal Hom `Hom_𝒪(M, N)` over `U`, read as the morphism
`M|_U ⟶ N|_U` of presheaves of modules on the slice site that it is. -/
def homOfSection (U : C) (a : internalHomObj O M N U) :
    (restrFun O U).obj M ⟶ (restrFun O U).obj N := a

/-- Iterated restriction of a section. -/
theorem restrictₛₗ_comp_apply {X Y Z : Cᵒᵖ} (i : X ⟶ Y) (j : Y ⟶ Z) (x : M.obj X) :
    M.restrictₛₗ (i ≫ j) x = M.restrictₛₗ j (M.restrictₛₗ i x) :=
  M.map_comp_apply i j x

/-- Restriction of a section is semilinear for the `CommRingCat`-valued presheaf of rings. -/
theorem restrictₛₗ_smul {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : O.obj X) (m : M.obj X) :
    M.restrictₛₗ f (r • m) = (O.map f).hom r • M.restrictₛₗ f m :=
  M.map_smul f r m

/-- Naturality of a morphism of presheaves of modules, in terms of `restrictₛₗ`. -/
theorem naturality_restrictₛₗ (f : M ⟶ N) {X Y : Cᵒᵖ} (g : X ⟶ Y) (x : M.obj X) :
    f.app Y (M.restrictₛₗ g x) = N.restrictₛₗ g (f.app X x) :=
  _root_.PresheafOfModules.naturality_apply f g x

end Retyping

/-! ### Morphisms out of a tensor product, read on pure tensors of sections -/

variable (F G H : _root_.PresheafOfModules.{w} (Oforget O))

/-- The value at an object of the site of a morphism out of a tensor product of presheaves of
modules, as a linear map on the tensor product of the sections there. -/
def tensorHomAt (b : F ⊗ G ⟶ H) (W : Cᵒᵖ) :
    TensorProduct (O.obj W) (F.obj W) (G.obj W) →ₗ[O.obj W] H.obj W :=
  (b.app W).hom

/-- A morphism out of a tensor product of presheaves of modules is determined by its values on
pure tensors of sections. -/
theorem tensorHom_ext {b b' : F ⊗ G ⟶ H}
    (h : ∀ (W : Cᵒᵖ) (x : F.obj W) (y : G.obj W),
      tensorHomAt O F G H b W (x ⊗ₜ y) = tensorHomAt O F G H b' W (x ⊗ₜ y)) : b = b' :=
  _root_.PresheafOfModules.hom_ext fun W ↦ ModuleCat.hom_ext (TensorProduct.ext' (h W))

/-- A family of linear maps on the tensor products of the sections, compatible with
restriction, assembles into a morphism `F ⊗ G ⟶ H`. -/
def tensorHomOfFamily
    (b : ∀ W : Cᵒᵖ, TensorProduct (O.obj W) (F.obj W) (G.obj W) →ₗ[O.obj W] H.obj W)
    (hb : ∀ {V W : Cᵒᵖ} (k : V ⟶ W) (x : F.obj V) (y : G.obj V),
      b W (F.restrictₛₗ k x ⊗ₜ G.restrictₛₗ k y) = H.restrictₛₗ k (b V (x ⊗ₜ y))) :
    F ⊗ G ⟶ H :=
  _root_.PresheafOfModules.Hom.mk (fun W ↦ ModuleCat.ofHom (b W)) fun k ↦
    ModuleCat.hom_ext (TensorProduct.ext' (hb k))

/-- The values of `tensorHomOfFamily` are the given family. -/
theorem tensorHomAt_tensorHomOfFamily
    (b : ∀ W : Cᵒᵖ, TensorProduct (O.obj W) (F.obj W) (G.obj W) →ₗ[O.obj W] H.obj W)
    (hb : ∀ {V W : Cᵒᵖ} (k : V ⟶ W) (x : F.obj V) (y : G.obj V),
      b W (F.restrictₛₗ k x ⊗ₜ G.restrictₛₗ k y) = H.restrictₛₗ k (b V (x ⊗ₜ y)))
    (W : Cᵒᵖ) : tensorHomAt O F G H (tensorHomOfFamily O F G H b hb) W = b W := rfl

/-- The value of a morphism out of a tensor product on a pure tensor commutes with
restriction. -/
theorem tensorHomAt_restrict (b : F ⊗ G ⟶ H) {W W' : Cᵒᵖ} (k : W ⟶ W')
    (x : F.obj W) (y : G.obj W) :
    tensorHomAt O F G H b W' (F.restrictₛₗ k x ⊗ₜ G.restrictₛₗ k y) =
      H.restrictₛₗ k (tensorHomAt O F G H b W (x ⊗ₜ y)) :=
  _root_.PresheafOfModules.naturality_apply b k (x ⊗ₜ y)

/-- Precomposing with `φ ▷ G` applies `φ` to the left tensor factor. -/
theorem tensorHomAt_whiskerRight {F' : _root_.PresheafOfModules.{w} (Oforget O)} (φ : F' ⟶ F)
    (b : F ⊗ G ⟶ H) (W : Cᵒᵖ) (x : F'.obj W) (y : G.obj W) :
    tensorHomAt O F' G H ((φ ▷ G) ≫ b) W (x ⊗ₜ y) =
      tensorHomAt O F G H b W (φ.app W x ⊗ₜ y) := rfl

/-! ### Sections of the internal Hom, read on the slice site -/

/-- The component at an object `f : V ⟶ U` of the slice site of a section of the internal Hom
`Hom_𝒪(G, H)` over `U`, as a linear map of the plain sections over `V`. -/
def homSectionCoeff (U : C) (a : internalHomObj O G H U) (V : Cᵒᵖ) (f : V.unop ⟶ U) :
    G.obj V →ₗ[O.obj V] H.obj V :=
  ((homOfSection O G H U a).app (op (Over.mk f))).hom

/-- A section of the internal Hom is determined by its components. -/
theorem homSection_ext (U : C) (a a' : internalHomObj O G H U)
    (h : ∀ (V : Cᵒᵖ) (f : V.unop ⟶ U) (t : G.obj V),
      homSectionCoeff O G H U a V f t = homSectionCoeff O G H U a' V f t) : a = a' :=
  show homOfSection O G H U a = homOfSection O G H U a' from
    _root_.PresheafOfModules.hom_ext fun V ↦
      ModuleCat.hom_ext (LinearMap.ext (h (op V.unop.left) V.unop.hom))

/-- The components of a section of the internal Hom are compatible with restriction. -/
theorem homSectionCoeff_restrict (U : C) (a : internalHomObj O G H U) {V W : Cᵒᵖ} (k : V ⟶ W)
    (f : V.unop ⟶ U) (t : G.obj V) :
    homSectionCoeff O G H U a W (k.unop ≫ f) (G.restrictₛₗ k t) =
      H.restrictₛₗ k (homSectionCoeff O G H U a V f t) :=
  _root_.PresheafOfModules.naturality_apply (homOfSection O G H U a)
    (show (op (Over.mk f) : (Over U)ᵒᵖ) ⟶ op (Over.mk (k.unop ≫ f)) from
      (Over.homMk k.unop rfl : (Over.mk (k.unop ≫ f) : Over U) ⟶ Over.mk f).op) t

/-! ### Currying a morphism out of a tensor product -/

/-- The curried map at a section `x` of `F` over `S` and an object `q : T ⟶ S` of the slice
site: it sends `y` to the value of `b` on the restriction of `x` tensored with `y`. -/
def homValue (b : F ⊗ G ⟶ H) {S : C} (x : F.obj (op S)) {T : C} (q : T ⟶ S) :
    G.obj (op T) →ₗ[O.obj (op T)] H.obj (op T) :=
  (tensorHomAt O F G H b (op T)).comp
    (TensorProduct.mk (O.obj (op T)) (F.obj (op T)) (G.obj (op T)) (F.restrictₛₗ q.op x))

/-- Unfolding `homValue`: it evaluates `b` on the restriction of `x` tensored with `y`. -/
theorem homValue_apply (b : F ⊗ G ⟶ H) {S : C} (x : F.obj (op S)) {T : C} (q : T ⟶ S)
    (y : G.obj (op T)) :
    homValue O F G H b x q y = tensorHomAt O F G H b (op T) (F.restrictₛₗ q.op x ⊗ₜ y) := rfl

/-- `homValue` is additive in the section of `F`. -/
theorem homValue_add_left (b : F ⊗ G ⟶ H) {S : C} (x x' : F.obj (op S)) {T : C} (q : T ⟶ S)
    (y : G.obj (op T)) :
    homValue O F G H b (x + x') q y =
      homValue O F G H b x q y + homValue O F G H b x' q y := by
  rw [homValue_apply, homValue_apply, homValue_apply, map_add, TensorProduct.add_tmul, map_add]

/-- `homValue` is semilinear in the section of `F`. -/
theorem homValue_smul_left (b : F ⊗ G ⟶ H) {S : C} (r : O.obj (op S)) (x : F.obj (op S))
    {T : C} (q : T ⟶ S) (y : G.obj (op T)) :
    homValue O F G H b (r • x) q y =
      (O.map q.op).hom r • homValue O F G H b x q y := by
  rw [homValue_apply, homValue_apply, restrictₛₗ_smul, ← TensorProduct.smul_tmul', map_smul]

/-- `homValue` is compatible with restriction in the slice. -/
theorem homValue_restrict (b : F ⊗ G ⟶ H) {S : C} (x : F.obj (op S)) {T T' : C} (q : T ⟶ S)
    (k : T' ⟶ T) (y : G.obj (op T)) :
    homValue O F G H b x (k ≫ q) (G.restrictₛₗ k.op y) =
      H.restrictₛₗ k.op (homValue O F G H b x q y) := by
  rw [homValue_apply, homValue_apply, op_comp, restrictₛₗ_comp_apply]
  exact tensorHomAt_restrict O F G H b k.op (F.restrictₛₗ q.op x) y

/-- Restricting the section of `F` reindexes the slice. -/
theorem homValue_base_restrict (b : F ⊗ G ⟶ H) {S S' : C} (k : S' ⟶ S) (x : F.obj (op S))
    {T : C} (q : T ⟶ S') (y : G.obj (op T)) :
    homValue O F G H b (F.restrictₛₗ k.op x) q y = homValue O F G H b x (q ≫ k) y := by
  rw [homValue_apply, homValue_apply, op_comp, restrictₛₗ_comp_apply]

/-- The currying of `b` at a section `x` of `F` over `S`: a morphism `G|_S ⟶ H|_S`, that is, a
section of the internal Hom `Hom_𝒪(G, H)` over `S`. -/
def homSection (b : F ⊗ G ⟶ H) {S : C} (x : F.obj (op S)) : internalHomObj O G H S :=
  _root_.PresheafOfModules.Hom.mk
    (fun V ↦ ofRestrHom O G H S V (homValue O F G H b x V.unop.hom))
    (fun {V _} f ↦ ModuleCat.hom_ext <| LinearMap.ext fun y ↦ by
      have h := homValue_restrict O F G H b x V.unop.hom f.unop.left y
      rwa [Over.w f.unop] at h)

/-- The components of a currying are the values `homValue`. -/
theorem homSectionCoeff_homSection (b : F ⊗ G ⟶ H) {S : C} (x : F.obj (op S)) (V : Cᵒᵖ)
    (f : V.unop ⟶ S) :
    homSectionCoeff O G H S (homSection O F G H b x) V f = homValue O F G H b x f := rfl

/-- The components of a currying, read on a section of `G`. -/
theorem homSectionCoeff_homSection_apply (b : F ⊗ G ⟶ H) {S : C} (x : F.obj (op S)) (V : Cᵒᵖ)
    (f : V.unop ⟶ S) (y : G.obj V) :
    homSectionCoeff O G H S (homSection O F G H b x) V f y =
      tensorHomAt O F G H b V (F.restrictₛₗ f.op x ⊗ₜ y) := rfl

/-- Currying at the sections over `S`, as an `𝒪(S)`-linear map into the internal Hom. -/
def homSectionLinearMap (b : F ⊗ G ⟶ H) (S : C) :
    F.obj (op S) →ₗ[O.obj (op S)] internalHomObj O G H S where
  toFun x := homSection O F G H b x
  map_add' x x' := _root_.PresheafOfModules.hom_ext fun V ↦
    ModuleCat.hom_ext (LinearMap.ext (homValue_add_left O F G H b x x' V.unop.hom))
  map_smul' r x := _root_.PresheafOfModules.hom_ext fun V ↦
    ModuleCat.hom_ext (LinearMap.ext (homValue_smul_left O F G H b r x V.unop.hom))

/-- Unfolding `homSectionLinearMap`. -/
theorem homSectionLinearMap_apply (b : F ⊗ G ⟶ H) (S : C) (x : F.obj (op S)) :
    homSectionLinearMap O F G H b S x = homSection O F G H b x := rfl

/-- Currying is compatible with restriction: the currying at a restricted section is the
restriction of the currying. -/
theorem homSection_base_restrict (b : F ⊗ G ⟶ H) {S S' : C} (k : S' ⟶ S) (x : F.obj (op S)) :
    homSection O F G H b (F.restrictₛₗ k.op x) = homRestr O G H k (homSection O F G H b x) :=
  homSection_ext O G H S' _ _ fun _ f ↦ homValue_base_restrict O F G H b k x f

/-- Currying is compatible with the restriction maps of the internal Hom presheaf. -/
theorem homSection_map (b : F ⊗ G ⟶ H) {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : F.obj X) :
    homSection O F G H b (F.restrictₛₗ f x) =
      (internalHom O G H).map f (homSection O F G H b x) :=
  homSection_base_restrict O F G H b f.unop x

/-- Restricting a global morphism `F ⟶ G` of presheaves of modules to the slice sites gives a
compatible family of sections of the internal Hom presheaf `Hom_𝒪(F, G)`. -/
theorem internalHom_map_restrFun_map {X Y : Cᵒᵖ} (f : X ⟶ Y) (φ : F ⟶ G) :
    (internalHom O F G).map f ((restrFun O X.unop).map φ) = (restrFun O Y.unop).map φ := rfl

/-! ### The free presheaf of modules on a representable presheaf -/

/-- The free presheaf of modules on the presheaf of sets represented by an object. -/
abbrev freeRepresentable (U : C) : _root_.PresheafOfModules.{w} (Oforget O) :=
  (_root_.PresheafOfModules.free (Oforget O)).obj (yoneda.obj U)

/-- The basis section of `free(U)` over `V` indexed by an arrow `V ⟶ U`. -/
def freeBasis (U : C) (V : Cᵒᵖ) (f : V.unop ⟶ U) : (freeRepresentable O U).obj V :=
  ModuleCat.freeMk f

/-- The restriction maps of `free(U)` on a basis section. -/
theorem freeRepresentable_restrictₛₗ_basis (U : C) {V W : Cᵒᵖ} (f : V ⟶ W) (g : V.unop ⟶ U) :
    (freeRepresentable O U).restrictₛₗ f (freeBasis O U V g) =
      freeBasis O U W (f.unop ≫ g) :=
  ModuleCat.freeDesc_apply _ _

/-- A morphism out of `free(U) ⊗ G` is determined by its values on a basis section tensored
with a section of `G`. -/
theorem freeTensorHom_ext (U : C) {b b' : freeRepresentable O U ⊗ G ⟶ H}
    (h : ∀ (V : Cᵒᵖ) (f : V.unop ⟶ U) (y : G.obj V),
      tensorHomAt O (freeRepresentable O U) G H b V (freeBasis O U V f ⊗ₜ y) =
        tensorHomAt O (freeRepresentable O U) G H b' V (freeBasis O U V f ⊗ₜ y)) : b = b' :=
  _root_.PresheafOfModules.hom_ext fun V ↦ ModuleCat.hom_ext <| TensorProduct.ext <|
    Finsupp.lhom_ext' fun f ↦ LinearMap.ext_ring (LinearMap.ext (h V f))

/-- A section of `free(U)` over `V`, read as a finitely supported function on the arrows
`V ⟶ U`. -/
def freeSectionOf (U : C) (V : Cᵒᵖ) (x : (freeRepresentable O U).obj V) :
    (V.unop ⟶ U) →₀ (O.obj V) := x

/-- A finitely supported function on the arrows `V ⟶ U`, read as a section of `free(U)`
over `V`. -/
def freeSectionTo (U : C) (V : Cᵒᵖ) (x : (V.unop ⟶ U) →₀ (O.obj V)) :
    (freeRepresentable O U).obj V := x

/-- `freeSectionTo` sends the zero function to the zero section. -/
@[simp] theorem freeSectionTo_zero (U : C) (V : Cᵒᵖ) : freeSectionTo O U V 0 = 0 := rfl

/-- `freeSectionTo` is additive. -/
@[simp] theorem freeSectionTo_add (U : C) (V : Cᵒᵖ) (x y : (V.unop ⟶ U) →₀ (O.obj V)) :
    freeSectionTo O U V (x + y) = freeSectionTo O U V x + freeSectionTo O U V y := rfl

/-- `freeSectionTo` commutes with scalar multiplication by sections of `O`. -/
@[simp] theorem freeSectionTo_smul (U : C) (V : Cᵒᵖ) (r : O.obj V)
    (x : (V.unop ⟶ U) →₀ (O.obj V)) :
    freeSectionTo O U V (r • x) = r • freeSectionTo O U V x := rfl

/-- A basis section is the function supported at one arrow with value one. -/
theorem freeSectionTo_single_one (U : C) (V : Cᵒᵖ) (f : V.unop ⟶ U) :
    freeSectionTo O U V (Finsupp.single f 1) = freeBasis O U V f := rfl

/-- A function supported at one arrow is a multiple of a basis section. -/
theorem freeSectionTo_single (U : C) (V : Cᵒᵖ) (f : V.unop ⟶ U) (r : O.obj V) :
    freeSectionTo O U V (Finsupp.single f r) = r • freeBasis O U V f := by
  rw [show (Finsupp.single f r : (V.unop ⟶ U) →₀ (O.obj V)) = r • Finsupp.single f 1 by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one],
    freeSectionTo_smul, freeSectionTo_single_one]

/-- The uncurrying of a section of the internal Hom over `U` at an object of the site: the
linear combination, with the coefficients of a section of `free(U)`, of the components of the
given section of the internal Hom. -/
def uncurryFreeAt (U : C) (a : internalHomObj O G H U) (V : Cᵒᵖ) :
    TensorProduct (O.obj V) ((freeRepresentable O U).obj V) (G.obj V) →ₗ[O.obj V] H.obj V :=
  TensorProduct.lift
    (show (freeRepresentable O U).obj V →ₗ[O.obj V] G.obj V →ₗ[O.obj V] H.obj V from
      Finsupp.linearCombination (O.obj V) (homSectionCoeff O G H U a V))

/-- The value of `uncurryFreeAt` on a basis section tensored with a section of `G`. -/
theorem uncurryFreeAt_tmul (U : C) (a : internalHomObj O G H U) (V : Cᵒᵖ) (f : V.unop ⟶ U)
    (t : G.obj V) :
    uncurryFreeAt O G H U a V (freeBasis O U V f ⊗ₜ t) = homSectionCoeff O G H U a V f t :=
  calc uncurryFreeAt O G H U a V (freeBasis O U V f ⊗ₜ t)
      = (Finsupp.linearCombination (O.obj V) (homSectionCoeff O G H U a V)
          (Finsupp.single f 1)) t := TensorProduct.lift.tmul _ _
    _ = homSectionCoeff O G H U a V f t := by
        rw [Finsupp.linearCombination_single, one_smul]

/-- `uncurryFreeAt` is compatible with restriction, checked on a finitely supported
function. -/
theorem uncurryFreeAt_restrict_aux (U : C) (a : internalHomObj O G H U) {V W : Cᵒᵖ} (k : V ⟶ W)
    (x : (V.unop ⟶ U) →₀ (O.obj V)) (t : G.obj V) :
    uncurryFreeAt O G H U a W
        ((freeRepresentable O U).restrictₛₗ k (freeSectionTo O U V x) ⊗ₜ G.restrictₛₗ k t) =
      H.restrictₛₗ k (uncurryFreeAt O G H U a V (freeSectionTo O U V x ⊗ₜ t)) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [freeSectionTo_add, map_add, TensorProduct.add_tmul, map_add, hx, hy,
      TensorProduct.add_tmul, map_add, map_add]
  | single f r =>
    rw [freeSectionTo_single, restrictₛₗ_smul O (freeRepresentable O U),
      freeRepresentable_restrictₛₗ_basis, ← TensorProduct.smul_tmul', map_smul,
      uncurryFreeAt_tmul, ← TensorProduct.smul_tmul', map_smul, uncurryFreeAt_tmul,
      restrictₛₗ_smul O H, homSectionCoeff_restrict]

/-- `uncurryFreeAt` is compatible with restriction. -/
theorem uncurryFreeAt_restrict (U : C) (a : internalHomObj O G H U) {V W : Cᵒᵖ} (k : V ⟶ W)
    (x : (freeRepresentable O U).obj V) (t : G.obj V) :
    uncurryFreeAt O G H U a W
        ((freeRepresentable O U).restrictₛₗ k x ⊗ₜ G.restrictₛₗ k t) =
      H.restrictₛₗ k (uncurryFreeAt O G H U a V (x ⊗ₜ t)) :=
  uncurryFreeAt_restrict_aux O G H U a k (freeSectionOf O U V x) t

/-- A section of the internal Hom over `U` gives back a morphism `free(U) ⊗ G ⟶ H`. -/
def tensorUncurryFree (U : C) (a : internalHomObj O G H U) :
    freeRepresentable O U ⊗ G ⟶ H :=
  tensorHomOfFamily O (freeRepresentable O U) G H (uncurryFreeAt O G H U a)
    (fun {_ _} k x y ↦ uncurryFreeAt_restrict O G H U a k x y)

/-- The value of `tensorUncurryFree` on a basis section tensored with a section of `G`. -/
theorem tensorUncurryFree_tmul (U : C) (a : internalHomObj O G H U) (V : Cᵒᵖ)
    (f : V.unop ⟶ U) (t : G.obj V) :
    tensorHomAt O (freeRepresentable O U) G H (tensorUncurryFree O G H U a) V
        (freeBasis O U V f ⊗ₜ t) = homSectionCoeff O G H U a V f t :=
  uncurryFreeAt_tmul O G H U a V f t

/-- The currying of a morphism `free(U) ⊗ G ⟶ H`: the section of the internal Hom
`Hom_𝒪(G, H)` over `U` obtained by evaluating at the identity basis section. -/
def tensorFreeHomCurry (U : C) (b : freeRepresentable O U ⊗ G ⟶ H) : internalHomObj O G H U :=
  homSection O (freeRepresentable O U) G H b (freeBasis O U (op U) (𝟙 U))

/-- The components of `tensorFreeHomCurry` are the values of `b` on a basis section. -/
theorem homSectionCoeff_tensorFreeHomCurry (U : C) (b : freeRepresentable O U ⊗ G ⟶ H)
    (V : Cᵒᵖ) (f : V.unop ⟶ U) (y : G.obj V) :
    homSectionCoeff O G H U (tensorFreeHomCurry O G H U b) V f y =
      tensorHomAt O (freeRepresentable O U) G H b V (freeBasis O U V f ⊗ₜ y) := by
  have h := homSectionCoeff_homSection_apply O (freeRepresentable O U) G H b
    (freeBasis O U (op U) (𝟙 U)) V f y
  rwa [freeRepresentable_restrictₛₗ_basis, Category.comp_id] at h

/-- Morphisms `free(U) ⊗ G ⟶ H` are the sections of the internal Hom `Hom_𝒪(G, H)` over `U`. -/
def tensorFreeHomEquiv (U : C) :
    (freeRepresentable O U ⊗ G ⟶ H) ≃ internalHomObj O G H U where
  toFun := tensorFreeHomCurry O G H U
  invFun := tensorUncurryFree O G H U
  left_inv b := freeTensorHom_ext O G H U fun V f y ↦ by
    rw [tensorUncurryFree_tmul, homSectionCoeff_tensorFreeHomCurry]
  right_inv a := homSection_ext O G H U _ _ fun V f t ↦ by
    rw [homSectionCoeff_tensorFreeHomCurry, tensorUncurryFree_tmul]

/-- Unfolding `tensorFreeHomEquiv`. -/
theorem tensorFreeHomEquiv_apply (U : C) (b : freeRepresentable O U ⊗ G ⟶ H) :
    tensorFreeHomEquiv O G H U b = tensorFreeHomCurry O G H U b := rfl

/-- The value of the inverse of `PresheafOfModules.freeYonedaEquiv` on the identity basis
section. -/
theorem freeYonedaEquiv_symm_app_basis_id (M : _root_.PresheafOfModules.{w} (Oforget O)) (U : C)
    (s : M.obj (op U)) :
    (_root_.PresheafOfModules.freeYonedaEquiv.symm s).app (op U) (freeBasis O U (op U) (𝟙 U)) =
      s :=
  _root_.PresheafOfModules.freeYonedaEquiv_symm_app M U s

/-- The value of the inverse of `PresheafOfModules.freeYonedaEquiv` on a basis section. -/
theorem freeYonedaEquiv_symm_app_basis (M : _root_.PresheafOfModules.{w} (Oforget O)) (U : C)
    (s : M.obj (op U)) (V : Cᵒᵖ) (f : V.unop ⟶ U) :
    (_root_.PresheafOfModules.freeYonedaEquiv.symm s).app V (freeBasis O U V f) =
      M.restrictₛₗ f.op s := by
  have h := naturality_restrictₛₗ O (freeRepresentable O U) M
    (_root_.PresheafOfModules.freeYonedaEquiv.symm s) f.op (freeBasis O U (op U) (𝟙 U))
  rwa [freeRepresentable_restrictₛₗ_basis, Category.comp_id,
    freeYonedaEquiv_symm_app_basis_id] at h

end Stacks.PresheafOfModules.TensorInternalHom

namespace Stacks.SheafOfModules.Invertible

open AlgebraicGeometry.SheafOfModules (IsInvertible)
open Stacks.SheafOfModules.TensorSheafification
open Stacks.PresheafOfModules.TensorInternalHom

variable {C : Type u} [Category.{w} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

section Pairing

/-- The monoidal structure `PresheafOfModulesOfCommRing.monoidalCategory` on presheaves of
modules over the structure sheaf of rings. -/
local instance monoidalCategoryStructureSheaf :
    MonoidalCategory (_root_.PresheafOfModules.{w} (structureSheaf O hO).obj) :=
  _root_.PresheafOfModulesOfCommRing.monoidalCategory (R := O)

/-- The underlying presheaf of modules of a sheaf of modules, read over the presheaf of rings
`Oforget O` that indexes the presheaf-level constructions. -/
def valPresheaf (M : _root_.SheafOfModules.{w} (structureSheaf O hO)) :
    _root_.PresheafOfModules.{w} (Oforget O) := M.val

/-- A morphism of sheaves of modules, read as a morphism of the underlying presheaves of
modules over `Oforget O`. -/
def valPresheafMap {M N : _root_.SheafOfModules.{w} (structureSheaf O hO)} (φ : M ⟶ N) :
    valPresheaf O hO M ⟶ valPresheaf O hO N := φ.val

/-- The pairing `M ⊗_𝒪 G ⟶ H` of presheaves of modules attached to an isomorphism
`ev : M ⊗_𝒪 G ≅ H` of sheaves of modules: the unit of sheafification followed by `ev`. -/
def tensorPairing (G M H : _root_.SheafOfModules.{w} (structureSheaf O hO))
    (ev : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (M)).obj (G)) ≅ H) :
    valPresheaf O hO M ⊗ valPresheaf O hO G ⟶ valPresheaf O hO H :=
  toSheafify O hO (M.val ⊗ G.val) ≫ ev.hom.val

/-- For an invertible `G` and an isomorphism `ev : M ⊗_𝒪 G ≅ H`, precomposing with the pairing
`M ⊗ G ⟶ H` is a bijection from the morphisms of presheaves of modules `A ⟶ M` onto the
morphisms `A ⊗ G ⟶ H`. -/
theorem tensorHom_bijective_of_isInvertible
    (G M H : _root_.SheafOfModules.{w} (structureSheaf O hO)) [IsInvertible O hO G]
    (ev : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (M)).obj (G)) ≅ H)
    (A : _root_.PresheafOfModules.{w} (structureSheaf O hO).obj) :
    Function.Bijective (fun f : A ⟶ M.val ↦
      (f ▷ G.val) ≫ toSheafify O hO (M.val ⊗ G.val) ≫ ev.hom.val) := by
  let a := sheafify O hO
  let adj := sheafifyAdjunction O hO
  let T := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, w, w, w, w}
    ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj G
  let η := toSheafify O hO A
  let q := a.map (η ▷ G.val)
  have : IsIso q :=
    isIso_sheafify_map_whiskerRight O hO η G.val (isIso_sheafify_map_toSheafify O hO A)
  let e : (A ⟶ M.val) ≃ (A ⊗ G.val ⟶ H.val) :=
    (adj.homEquiv A M).symm.trans
      ((Functor.FullyFaithful.ofFullyFaithful T).homEquiv.trans
        ((Iso.homCongr (asIso q).symm ev).trans (adj.homEquiv (A ⊗ G.val) H)))
  have he (f : A ⟶ M.val) :
      e f = (f ▷ G.val) ≫ toSheafify O hO (M.val ⊗ G.val) ≫ ev.hom.val := by
    let g := (adj.homEquiv A M).symm f
    have hg : η ≫ g.val = f := (adj.homEquiv A M).apply_symm_apply f
    have hwhisker : (η ▷ G.val) ≫ (g.val ▷ G.val) = f ▷ G.val :=
      (MonoidalCategory.comp_whiskerRight η g.val G.val).symm.trans
        (congrArg (fun z ↦ z ▷ G.val) hg)
    have hcomp : a.map (η ▷ G.val) ≫ a.map (g.val ▷ G.val) = a.map (f ▷ G.val) :=
      (a.map_comp _ _).symm.trans (congrArg a.map hwhisker)
    have hn : (f ▷ G.val) ≫ adj.unit.app (M.val ⊗ G.val) =
        adj.unit.app (A ⊗ G.val) ≫ (a.map (f ▷ G.val)).val :=
      adj.unit.naturality (f ▷ G.val)
    show adj.unit.app (A ⊗ G.val) ≫
      ((a.map (η ▷ G.val) ≫ a.map (g.val ▷ G.val)) ≫ ev.hom).val = _
    calc adj.unit.app (A ⊗ G.val) ≫
          ((a.map (η ▷ G.val) ≫ a.map (g.val ▷ G.val)) ≫ ev.hom).val
        = (adj.unit.app (A ⊗ G.val) ≫ (a.map (f ▷ G.val)).val) ≫ ev.hom.val := by
          rw [hcomp]; exact (Category.assoc _ _ _).symm
      _ = ((f ▷ G.val) ≫ adj.unit.app (M.val ⊗ G.val)) ≫ ev.hom.val :=
          congrArg (fun z ↦ z ≫ ev.hom.val) hn.symm
      _ = (f ▷ G.val) ≫ toSheafify O hO (M.val ⊗ G.val) ≫ ev.hom.val :=
          Category.assoc _ _ _
  convert e.bijective using 1
  exact funext fun f ↦ (he f).symm

/-- For an invertible `G` and an isomorphism `ev : M ⊗_𝒪 G ≅ H`, precomposing with
`tensorPairing` is a bijection from the morphisms `A ⟶ M` of presheaves of modules over
`Oforget O` onto the morphisms `A ⊗ G ⟶ H`. -/
theorem tensorHom_bijective (G M H : _root_.SheafOfModules.{w} (structureSheaf O hO))
    [IsInvertible O hO G] (ev : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (M)).obj (G)) ≅ H)
    (A : _root_.PresheafOfModules.{w} (Oforget O)) :
    Function.Bijective (fun f : A ⟶ valPresheaf O hO M ↦
      (f ▷ valPresheaf O hO G) ≫ tensorPairing O hO G M H ev) :=
  tensorHom_bijective_of_isInvertible O hO G M H ev A

end Pairing

/-- For an invertible `G` and an isomorphism `ev : M ⊗_𝒪 G ≅ H`, currying against the pairing
`M ⊗ G ⟶ H` is bijective on the sections over every object of the site. -/
theorem homSectionLinearMap_bijective
    (G M H : _root_.SheafOfModules.{w} (structureSheaf O hO)) [IsInvertible O hO G]
    (ev : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (M)).obj (G)) ≅ H) (U : C) :
    Function.Bijective (homSectionLinearMap O (valPresheaf O hO M) (valPresheaf O hO G)
      (valPresheaf O hO H) (tensorPairing O hO G M H ev) U) := by
  have heq : (fun s : (valPresheaf O hO M).obj (op U) ↦
      tensorFreeHomEquiv O (valPresheaf O hO G) (valPresheaf O hO H) U
        ((_root_.PresheafOfModules.freeYonedaEquiv.symm s ▷ valPresheaf O hO G) ≫
          tensorPairing O hO G M H ev)) =
      homSectionLinearMap O (valPresheaf O hO M) (valPresheaf O hO G) (valPresheaf O hO H)
        (tensorPairing O hO G M H ev) U := by
    funext s
    refine homSection_ext O (valPresheaf O hO G) (valPresheaf O hO H) U _ _ fun V f t ↦ ?_
    rw [tensorFreeHomEquiv_apply, homSectionCoeff_tensorFreeHomCurry,
      tensorHomAt_whiskerRight, freeYonedaEquiv_symm_app_basis, homSectionLinearMap_apply,
      homSectionCoeff_homSection_apply]
  rw [← heq]
  exact (tensorFreeHomEquiv O (valPresheaf O hO G) (valPresheaf O hO H) U).bijective.comp
    ((tensorHom_bijective O hO G M H ev (freeRepresentable O U)).comp
      (_root_.PresheafOfModules.freeYonedaEquiv
        (M := valPresheaf O hO M) (X := U)).symm.bijective)

/-- The comparison of the sections of `M` over an object of the site with the sections of the
internal Hom `Hom_𝒪(G, H)`, for an invertible `G` and an isomorphism `ev : M ⊗_𝒪 G ≅ H`. -/
def tensorCurryLinearEquiv
    (G M H : _root_.SheafOfModules.{w} (structureSheaf O hO)) [IsInvertible O hO G]
    (ev : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (M)).obj (G)) ≅ H) (U : C) :
    (valPresheaf O hO M).obj (op U) ≃ₗ[O.obj (op U)]
      internalHomObj O (valPresheaf O hO G) (valPresheaf O hO H) U :=
  LinearEquiv.ofBijective
    (homSectionLinearMap O (valPresheaf O hO M) (valPresheaf O hO G) (valPresheaf O hO H)
      (tensorPairing O hO G M H ev) U)
    (homSectionLinearMap_bijective O hO G M H ev U)

/-- The comparison commutes with the restriction maps of `M` and of the internal Hom. -/
theorem tensorCurryLinearEquiv_natural
    (G M H : _root_.SheafOfModules.{w} (structureSheaf O hO)) [IsInvertible O hO G]
    (ev : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (M)).obj (G)) ≅ H) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (s : (valPresheaf O hO M).obj X) :
    tensorCurryLinearEquiv O hO G M H ev Y.unop ((valPresheaf O hO M).restrictₛₗ f s) =
      (internalHom O (valPresheaf O hO G) (valPresheaf O hO H)).map f
        (tensorCurryLinearEquiv O hO G M H ev X.unop s) :=
  homSection_map O (valPresheaf O hO M) (valPresheaf O hO G) (valPresheaf O hO H) _ f s

/-- The comparison is pinned down by the pairing: the morphism `G|_U ⟶ H|_U` attached to a
section `s` of `M` over `U` takes a section `t` of `G` over an object `f : V ⟶ U` of the slice
site to the value of the pairing `M ⊗_𝒪 G ⟶ H` on the restriction of `s` tensored with `t`. -/
theorem tensorCurryLinearEquiv_apply
    (G M H : _root_.SheafOfModules.{w} (structureSheaf O hO)) [IsInvertible O hO G]
    (ev : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (M)).obj (G)) ≅ H) (U : C) (s : (valPresheaf O hO M).obj (op U)) (V : Cᵒᵖ)
    (f : V.unop ⟶ U) (t : (valPresheaf O hO G).obj V) :
    homSectionCoeff O (valPresheaf O hO G) (valPresheaf O hO H) U
        (tensorCurryLinearEquiv O hO G M H ev U s) V f t =
      tensorHomAt O (valPresheaf O hO M) (valPresheaf O hO G) (valPresheaf O hO H)
        (tensorPairing O hO G M H ev) V
        ((valPresheaf O hO M).restrictₛₗ f.op s ⊗ₜ t) :=
  homSectionCoeff_homSection_apply O (valPresheaf O hO M) (valPresheaf O hO G)
    (valPresheaf O hO H) (tensorPairing O hO G M H ev) s V f t

end Stacks.SheafOfModules.Invertible

end
