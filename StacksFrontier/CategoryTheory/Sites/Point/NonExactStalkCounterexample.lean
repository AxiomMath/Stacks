module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

/-!
# A functor to sets whose stalk functor is not exact

Stacks tag 00YD (Remark 7.33.4): an explicit site `𝒞` and a point-candidate functor `u`
whose site-theoretic stalk functor fails to be exact.

The category `𝒞` (Definition 1) has two objects `X` and `U` and one non-identity arrow
`f : U ⟶ X`, so composition is forced; `X` is final and `𝒞` has all fibre products. It
carries the trivial topology, so every presheaf of sets is a sheaf, and a presheaf `ℱ`
(Definition 2) is exactly the data of `A = ℱ(X)`, `B = ℱ(U)` and a restriction
`r = ℱ(f) : A → B`. The functor `u : 𝒞 ⥤ Set` (Definition 3) has `u(X) = PUnit` a
singleton, `u(U) = Bool` a two-element set, and `u(f)` the unique constant map. Its
neighbourhood category `𝒞_u = u.Elements` (Definition 4) has objects the pairs `(V, x)`
with `x ∈ u(V)`, and the stalk of `ℱ` at `p = u` is the colimit
`ℱ_p = colim_{(V,x) ∈ (𝒞_u)ᵒᵖ} ℱ(V)` (Definition 5; tag 04EH, Equation 7.32.1.1).
Alongside it, Definition 4 also introduces the pushout `B ⨿_A B` of the span
`B ←r A →r B`, as a functor `pushoutFunctor`.

## Main results

* `stalkIsoPushout` (Statement 1): the stalk functor is naturally isomorphic to
  `(A, B, r) ↦ B ⨿_A B`.
* `stalkFunctor_not_preservesMono` (Statement 2): the stalk functor does not preserve
  monomorphisms. This is shown for the pushout functor
  (`pushoutFunctor_not_preservesMono`) via the mono `(∅, {1}, ∅ → {1}) ⟶ ({1}, {1}, id)`,
  whose pushout map `{1} ⨿_∅ {1} → {1} ⨿_{1} {1}` collapses two elements to one, and
  transported along Statement 1.
* `u_not_point` (Statement 3): failing to preserve monomorphisms, the stalk functor is not
  left exact, which is precisely the obstruction to `u` being a point of `𝒞` (tag 00Y5).

This `u` does not satisfy the general fibre-product condition (2') of 00YD: for
`V = V' = U`, `W = X` and both arrows `f`, the induced diagonal `u(U) → u(U) × u(U)` is
not surjective. That condition is therefore not asserted; the content formalized here is
exactly Statements 1–3.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Counterexample

universe v u

/-! ## Definition 1: the category `𝒞`. -/

/-- Objects of the site `𝒞`. -/
inductive Obj where
  | X : Obj
  | U : Obj
deriving DecidableEq

open Obj

/-- Morphisms of `𝒞`: identities `id_X`, `id_U`, and the unique arrow `f : U → X`. -/
inductive Hom : Obj → Obj → Type where
  | idX : Hom X X
  | idU : Hom U U
  | f   : Hom U X

open Hom

/-- The identity morphisms of `𝒞`. -/
def homId : ∀ a : Obj, Hom a a
  | X => idX
  | U => idU

/-- Composition in `𝒞` (forced by the morphism structure). -/
def homComp : ∀ {a b c : Obj}, Hom a b → Hom b c → Hom a c
  | _, _, _, idX, g => g
  | _, _, _, idU, g => g
  | _, _, _, f, idX => f

/-- The category structure on `𝒞`. -/
instance instCategoryObj : Category Obj where
  Hom a b := Hom a b
  id a := homId a
  comp h g := homComp h g
  id_comp := by rintro a b ⟨⟩ <;> rfl
  comp_id := by rintro a b ⟨⟩ <;> rfl
  assoc := by rintro a b c d ⟨⟩ ⟨⟩ ⟨⟩ <;> rfl

/-- The unique non-identity arrow `f : U ⟶ X`, packaged as a categorical morphism. -/
abbrev fHom : (U : Obj) ⟶ X := Hom.f

/-- `X` is a terminal (final) object of `𝒞`: each object has a unique map to `X`. -/
def isTerminalX : Limits.IsTerminal (X : Obj) :=
  Limits.IsTerminal.ofUniqueHom
    (fun a => match a with | X => idX | U => f)
    (by rintro a ⟨⟩ <;> rfl)

/-! ## Definition 3: the functor `u : 𝒞 → Set`. -/

/-- Object part of `u`: `u(X) = {∗}` (`PUnit`), `u(U) = {∗₁, ∗₂}` (`Bool`). -/
@[implicit_reducible]
def uObj : Obj → Type
  | X => PUnit
  | U => Bool

/-- The functor `u : 𝒞 → Set` with `u(X) = PUnit`, `u(U) = Bool`, `u(id) = id`,
and `u(f)` the unique (constant) map. -/
@[implicit_reducible]
def u : Obj ⥤ Type where
  obj := uObj
  map {a b} h :=
    match a, b, h with
    | _, _, idX => TypeCat.ofHom (fun (x : uObj X) => x)
    | _, _, idU => TypeCat.ofHom (fun (x : uObj U) => x)
    | _, _, f => TypeCat.ofHom (fun (_ : uObj U) => (PUnit.unit : uObj X))
  map_id := by rintro ⟨⟩ <;> rfl
  map_comp := by rintro a b c ⟨⟩ ⟨⟩ <;> rfl

/-- Condition: `u(X)` is a singleton (`= PUnit`). -/
theorem u_obj_X : u.obj X = PUnit := rfl

/-- `u(U)` is the two-element set `Bool`. -/
theorem u_obj_U : u.obj U = Bool := rfl

/-- `u(f)` is the constant (unique) map `u(U) → u(X)`. -/
theorem u_map_f (b : Bool) : u.map fHom b = PUnit.unit := rfl

/-! ## Presheaves on `𝒞`. -/

/-- A presheaf of sets on `𝒞` (= a sheaf, since the topology is trivial). -/
abbrev Presheaf := Objᵒᵖ ⥤ Type

/-- The restriction map `r = ℱ(f) : ℱ(X) → ℱ(U)` of a presheaf `ℱ` (Definition 2). -/
def restr (ℱ : Presheaf) (a : ℱ.obj (Opposite.op X)) : ℱ.obj (Opposite.op U) :=
  ℱ.map (Quiver.Hom.op fHom) a

/-- Naturality of restriction: `φ_U ∘ r_ℱ = r_𝒢 ∘ φ_X`. -/
theorem restr_naturality {ℱ 𝒢 : Presheaf} (φ : ℱ ⟶ 𝒢) (a : ℱ.obj (Opposite.op X)) :
    φ.app (Opposite.op U) (restr ℱ a) = restr 𝒢 (φ.app (Opposite.op X) a) :=
  NatTrans.naturality_apply φ (Quiver.Hom.op fHom) a

/-! ## Definitions 4 & 5: the neighbourhood category and the stalk. -/

/-- The neighbourhood category `𝒞_u` of the point `u`: the category of elements
of `u`. Objects are pairs `(V, x)` with `x ∈ u(V)`; a morphism `(V, x) → (V', x')`
is `α : V → V'` with `u(α)(x) = x'`. -/
abbrev Nbhd := u.Elements

/-- The diagram `(𝒞_u)ᵒᵖ → 𝒞ᵒᵖ → Set` underlying the stalk of a presheaf `ℱ`. -/
@[implicit_reducible]
def stalkDiagram (ℱ : Presheaf) : Nbhdᵒᵖ ⥤ Type :=
  (CategoryOfElements.π u).op ⋙ ℱ

/-- Definition 5: the site-theoretic stalk functor `PSh(𝒞) ⥤ Set` at the point
`p = u`, namely `ℱ ↦ colim_{(V,x) ∈ (𝒞_u)ᵒᵖ} ℱ(V)`, with the induced map on
morphisms (Stacks Tag 04EH). -/
@[implicit_reducible]
noncomputable def stalkFunctor : Presheaf ⥤ Type where
  obj ℱ := colimit (stalkDiagram ℱ)
  map φ := colimMap (Functor.whiskerLeft (CategoryOfElements.π u).op φ)
  map_id ℱ := colimit.hom_ext fun j => by simp [stalkDiagram]
  map_comp φ ψ := colimit.hom_ext fun j => by simp [stalkDiagram]

/-- The stalk of `ℱ` is the colimit of its stalk diagram. -/
theorem stalkFunctor_obj (ℱ : Presheaf) :
    stalkFunctor.obj ℱ = colimit (stalkDiagram ℱ) := rfl

/-- The stalk functor acts on morphisms by the induced map of colimits. -/
theorem stalkFunctor_map {ℱ 𝒢 : Presheaf} (φ : ℱ ⟶ 𝒢) :
    stalkFunctor.map φ = colimMap (Functor.whiskerLeft (CategoryOfElements.π u).op φ) := rfl

/-! ### Definition 4: the pushout functor `(A, B, r) ↦ B ⨿_A B`. -/

/-- The gluing relation on `B ⊔ B` defining the pushout `B ⨿_A B`: identify
`inl (r a)` with `inr (r a)` for every `a ∈ A`. -/
inductive PushoutRel (ℱ : Presheaf) :
    (ℱ.obj (Opposite.op U) ⊕ ℱ.obj (Opposite.op U)) →
    (ℱ.obj (Opposite.op U) ⊕ ℱ.obj (Opposite.op U)) → Prop
  | glue (a : ℱ.obj (Opposite.op X)) :
      PushoutRel ℱ (Sum.inl (restr ℱ a)) (Sum.inr (restr ℱ a))

/-- The pushout `B ⨿_A B` of the span `B ←r A →r B` (Definition 4). -/
@[implicit_reducible]
def PushoutObj (ℱ : Presheaf) : Type := Quot (PushoutRel ℱ)

/-- The left inclusion `B → B ⨿_A B`. -/
@[implicit_reducible]
def PushoutObj.inl (ℱ : Presheaf) (b : ℱ.obj (Opposite.op U)) : PushoutObj ℱ :=
  Quot.mk _ (Sum.inl b)

/-- The right inclusion `B → B ⨿_A B`. -/
@[implicit_reducible]
def PushoutObj.inr (ℱ : Presheaf) (b : ℱ.obj (Opposite.op U)) : PushoutObj ℱ :=
  Quot.mk _ (Sum.inr b)

/-- The induced map on pushouts `B ⨿_A B → B' ⨿_{A'} B'` of a morphism of
presheaves `φ` (Definition 4): `[inl b] ↦ [inl (φ_U b)]`, `[inr b] ↦ [inr (φ_U b)]`. -/
def PushoutObj.map {ℱ 𝒢 : Presheaf} (φ : ℱ ⟶ 𝒢) : PushoutObj ℱ → PushoutObj 𝒢 :=
  Quot.lift
    (fun x => match x with
      | Sum.inl b => PushoutObj.inl 𝒢 (φ.app (Opposite.op U) b)
      | Sum.inr b => PushoutObj.inr 𝒢 (φ.app (Opposite.op U) b))
    (by
      rintro _ _ ⟨a⟩
      dsimp only
      rw [restr_naturality φ a]
      exact Quot.sound (PushoutRel.glue (φ.app (Opposite.op X) a)))

/-- `PushoutObj.map φ` sends the left inclusion of `b` to the left inclusion of `φ_U b`. -/
@[simp] theorem PushoutObj.map_inl {ℱ 𝒢 : Presheaf} (φ : ℱ ⟶ 𝒢)
    (b : ℱ.obj (Opposite.op U)) :
    PushoutObj.map φ (PushoutObj.inl ℱ b) = PushoutObj.inl 𝒢 (φ.app (Opposite.op U) b) :=
  rfl

/-- `PushoutObj.map φ` sends the right inclusion of `b` to the right inclusion of `φ_U b`. -/
@[simp] theorem PushoutObj.map_inr {ℱ 𝒢 : Presheaf} (φ : ℱ ⟶ 𝒢)
    (b : ℱ.obj (Opposite.op U)) :
    PushoutObj.map φ (PushoutObj.inr ℱ b) = PushoutObj.inr 𝒢 (φ.app (Opposite.op U) b) :=
  rfl

/-- `PushoutObj.map` takes the identity morphism of `ℱ` to the identity of `B ⨿_A B`. -/
theorem PushoutObj.map_id (ℱ : Presheaf) :
    PushoutObj.map (𝟙 ℱ) = (id : PushoutObj ℱ → PushoutObj ℱ) := by
  funext q
  induction q using Quot.ind with
  | _ x => cases x <;> rfl

/-- `PushoutObj.map` turns composition of presheaf morphisms into composition of the induced
maps on pushouts. -/
theorem PushoutObj.map_comp {ℱ 𝒢 ℋ : Presheaf} (φ : ℱ ⟶ 𝒢) (ψ : 𝒢 ⟶ ℋ) :
    PushoutObj.map (φ ≫ ψ) =
      (PushoutObj.map ψ) ∘ (PushoutObj.map φ) := by
  funext q
  induction q using Quot.ind with
  | _ x => cases x <;> rfl

/-- Definition 4 as a functor: the pushout functor `PSh(𝒞) ⥤ Set`,
`(A, B, r) ↦ B ⨿_A B`. -/
@[implicit_reducible]
def pushoutFunctor : Presheaf ⥤ Type where
  obj := PushoutObj
  map φ := TypeCat.ofHom (PushoutObj.map φ)
  map_id ℱ := by ext q; exact congrFun (PushoutObj.map_id ℱ) q
  map_comp φ ψ := by ext q; exact congrFun (PushoutObj.map_comp φ ψ) q

/-- The pushout functor acts on morphisms by `PushoutObj.map`. -/
theorem pushoutFunctor_map_apply {ℱ 𝒢 : Presheaf} (φ : ℱ ⟶ 𝒢) (q : PushoutObj ℱ) :
    pushoutFunctor.map φ q = PushoutObj.map φ q :=
  rfl

/-! ## Statement 1: the stalk functor equals the pushout functor. -/

/-- An `Nbhd`-morphism whose underlying `Obj`-morphism is the identity induces the
identity on the stalk diagram. -/
theorem stalkCocone_nbhd_map_id (ℱ : Presheaf) {p : Nbhd} (g : p ⟶ p)
    (hval : g.val = 𝟙 p.1) :
    (stalkDiagram ℱ).map (Opposite.op g) = 𝟙 ((stalkDiagram ℱ).obj (Opposite.op p)) := by
  have hg : g = 𝟙 p := CategoryOfElements.ext u g (𝟙 p) (by rw [hval, CategoryOfElements.id_val])
  rw [hg]
  exact (stalkDiagram ℱ).map_id _

/-- The constructor `Hom.idX` is the categorical identity of `X`; this is the hypothesis needed
to apply `stalkCocone_nbhd_map_id` in the `idX` case of the naturality check for `stalkCocone`. -/
theorem stalkCocone_idX_eq : (Hom.idX : (X : Obj) ⟶ X) = 𝟙 X := rfl

/-- The constructor `Hom.idU` is the categorical identity of `U`; the counterpart of
`stalkCocone_idX_eq` for the `idU` case. -/
theorem stalkCocone_idU_eq : (Hom.idU : (U : Obj) ⟶ U) = 𝟙 U := rfl

/-- The cocone on the stalk diagram of `ℱ` with apex `PushoutObj ℱ = B ⨿_A B`. -/
@[implicit_reducible]
noncomputable def stalkCocone (ℱ : Presheaf) : Cocone (stalkDiagram ℱ) where
  pt := PushoutObj ℱ
  ι := by
    refine NatTrans.mk (fun j => ?_) ?_
    · obtain ⟨⟨V, x⟩⟩ := j
      match V, x with
      | X, _ => exact TypeCat.ofHom (fun a => PushoutObj.inl ℱ (restr ℱ a))
      | U, false => exact TypeCat.ofHom (fun b => PushoutObj.inl ℱ b)
      | U, true => exact TypeCat.ofHom (fun b => PushoutObj.inr ℱ b)
    · rintro ⟨⟨V, x⟩⟩ ⟨⟨V', x'⟩⟩ ⟨(_|_|_), hα⟩
      · cases x; cases x'
        rw [stalkCocone_nbhd_map_id ℱ (p := ⟨X, PUnit.unit⟩) ⟨Hom.idX, hα⟩ stalkCocone_idX_eq]
        ext a; rfl
      · have hxx : x' = x := hα
        subst hxx
        rw [stalkCocone_nbhd_map_id ℱ (p := ⟨U, x'⟩) ⟨Hom.idU, hα⟩ stalkCocone_idU_eq]
        ext a; rfl
      · cases x
        cases x' with
        | false =>
          ext a
          dsimp only [TypeCat.Fun.toFun_apply, types_comp_apply, TypeCat.hom_ofHom,
            TypeCat.Fun.coe_mk, Functor.const_obj_map, types_id_apply, stalkDiagram,
            Functor.comp_map, Functor.op_map, CategoryOfElements.π_map, Quiver.Hom.unop_op, restr]
          rfl
        | true =>
          ext a
          change PushoutObj.inr ℱ (restr ℱ a) = PushoutObj.inl ℱ (restr ℱ a)
          exact (Quot.sound (PushoutRel.glue a)).symm

/-- The leg of `stalkCocone ℱ` at `(X, ∗)` is `a ↦ [inl (r a)]`. -/
theorem stalkCocone_ι_app_X (ℱ : Presheaf) (x : u.obj X) (a : ℱ.obj (Opposite.op X)) :
    (stalkCocone ℱ).ι.app (Opposite.op (u.elementsMk X x)) a = PushoutObj.inl ℱ (restr ℱ a) :=
  rfl

/-- The leg of `stalkCocone ℱ` at `(U, ∗₁)` is `inl`. -/
theorem stalkCocone_ι_app_U_false (ℱ : Presheaf) (b : ℱ.obj (Opposite.op U)) :
    (stalkCocone ℱ).ι.app (Opposite.op (u.elementsMk U false)) b = PushoutObj.inl ℱ b :=
  rfl

/-- The leg of `stalkCocone ℱ` at `(U, ∗₂)` is `inr`. -/
theorem stalkCocone_ι_app_U_true (ℱ : Presheaf) (b : ℱ.obj (Opposite.op U)) :
    (stalkCocone ℱ).ι.app (Opposite.op (u.elementsMk U true)) b = PushoutObj.inr ℱ b :=
  rfl

private def nbhdFArrow (b : Bool) :
    (u.elementsMk U b) ⟶ (u.elementsMk X PUnit.unit) :=
  CategoryOfElements.homMk _ _ Hom.f rfl

private theorem stalkCocone_desc_aux (ℱ : Presheaf) (s : Cocone (stalkDiagram ℱ))
    (b : Bool) (a : ℱ.obj (Opposite.op X)) :
    s.ι.app (Opposite.op (u.elementsMk U b)) (restr ℱ a)
      = s.ι.app (Opposite.op (u.elementsMk X PUnit.unit)) a :=
  NatTrans.naturality_apply s.ι (nbhdFArrow b).op a

/-- The map `B ⨿_A B → s.pt` induced by an arbitrary cocone `s` on the stalk diagram: send
`[inl b]` to `s.ι (U, false) b` and `[inr b]` to `s.ι (U, true) b`. It respects `PushoutRel`
because both legs agree on restrictions from `X`, by `stalkCocone_desc_aux`. -/
noncomputable def stalkCocone_descFun (ℱ : Presheaf) (s : Cocone (stalkDiagram ℱ)) :
    PushoutObj ℱ → s.pt :=
  Quot.lift
    (fun x => match x with
      | Sum.inl b => s.ι.app (Opposite.op (u.elementsMk U false)) b
      | Sum.inr b => s.ι.app (Opposite.op (u.elementsMk U true)) b)
    (by
      rintro _ _ ⟨a⟩
      dsimp only
      rw [stalkCocone_desc_aux ℱ s false a, stalkCocone_desc_aux ℱ s true a])

private theorem stalkCocone_descFun_inl (ℱ : Presheaf) (s : Cocone (stalkDiagram ℱ))
    (b : ℱ.obj (Opposite.op U)) :
    stalkCocone_descFun ℱ s (PushoutObj.inl ℱ b)
      = s.ι.app (Opposite.op (u.elementsMk U false)) b := rfl

private theorem stalkCocone_descFun_inr (ℱ : Presheaf) (s : Cocone (stalkDiagram ℱ))
    (b : ℱ.obj (Opposite.op U)) :
    stalkCocone_descFun ℱ s (PushoutObj.inr ℱ b)
      = s.ι.app (Opposite.op (u.elementsMk U true)) b := rfl

/-- `stalkCocone ℱ` is a colimit cocone, with `stalkCocone_descFun` as its descent map. This is
what computes the stalk of `ℱ` at `p = u` as `B ⨿_A B`, and hence the content of Statement 1. -/
noncomputable def stalkCoconeIsColimit (ℱ : Presheaf) : IsColimit (stalkCocone ℱ) where
  desc s := TypeCat.ofHom (stalkCocone_descFun ℱ s)
  fac s j := by
    obtain ⟨⟨V, x⟩⟩ := j
    ext a
    match V, x with
    | X, _ =>
      dsimp only [TypeCat.Fun.toFun_apply, types_comp_apply, TypeCat.hom_ofHom,
        TypeCat.Fun.coe_mk]
      rw [stalkCocone_ι_app_X, stalkCocone_descFun_inl, stalkCocone_desc_aux ℱ s false a]
      rfl
    | U, false => rfl
    | U, true => rfl
  uniq s m hm := by
    ext q
    induction q using Quot.ind with
    | _ x =>
      cases x with
      | inl b =>
        have hb := ConcreteCategory.congr_hom (hm (Opposite.op (u.elementsMk U false))) b
        dsimp only [TypeCat.Fun.toFun_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk]
        rw [types_comp_apply, stalkCocone_ι_app_U_false] at hb
        exact hb.trans (stalkCocone_descFun_inl ℱ s b).symm
      | inr b =>
        have hb := ConcreteCategory.congr_hom (hm (Opposite.op (u.elementsMk U true))) b
        dsimp only [TypeCat.Fun.toFun_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk]
        rw [types_comp_apply, stalkCocone_ι_app_U_true] at hb
        exact hb.trans (stalkCocone_descFun_inr ℱ s b).symm

/-- Per-object iso `stalkFunctor.obj ℱ ≅ pushoutFunctor.obj ℱ`. -/
noncomputable def stalkObjIso (ℱ : Presheaf) :
    stalkFunctor.obj ℱ ≅ pushoutFunctor.obj ℱ :=
  colimit.isoColimitCocone ⟨stalkCocone ℱ, stalkCoconeIsColimit ℱ⟩

/-- The per-object isos `stalkObjIso` are natural in `ℱ`. -/
theorem stalkObjIso_naturality {ℱ 𝒢 : Presheaf} (φ : ℱ ⟶ 𝒢) :
    stalkFunctor.map φ ≫ (stalkObjIso 𝒢).hom
      = (stalkObjIso ℱ).hom ≫ pushoutFunctor.map φ := by
  apply colimit.hom_ext
  intro j
  rw [stalkFunctor_map, ι_colimMap_assoc, stalkObjIso, stalkObjIso,
    colimit.isoColimitCocone_ι_hom, colimit.isoColimitCocone_ι_hom_assoc]
  obtain ⟨⟨V, x⟩⟩ := j
  ext a
  dsimp only [Functor.comp_obj, Functor.op_obj, Functor.whiskerLeft_app, TypeCat.Fun.toFun_apply,
    types_comp_apply, CategoryOfElements.π_obj]
  rw [pushoutFunctor_map_apply]
  match V, x with
  | X, x =>
      rw [stalkCocone_ι_app_X, stalkCocone_ι_app_X, PushoutObj.map_inl, restr_naturality]
      rfl
  | U, false =>
      rw [stalkCocone_ι_app_U_false, stalkCocone_ι_app_U_false, PushoutObj.map_inl]
      rfl
  | U, true =>
      rw [stalkCocone_ι_app_U_true, stalkCocone_ι_app_U_true, PushoutObj.map_inr]
      rfl

/-- **Statement 1.** For the site `𝒞` and the functor `u`, the site-theoretic
stalk functor of Definition 5 is naturally isomorphic to the pushout functor
`(A, B, r) ↦ B ⨿_A B` of Definition 4 (Stacks Tag 00YD computation). -/
theorem stalkIsoPushout : Nonempty (stalkFunctor ≅ pushoutFunctor) :=
  ⟨NatIso.ofComponents stalkObjIso (fun φ => stalkObjIso_naturality φ)⟩

/-! ## Statement 2: the stalk functor is not exact (does not preserve monos). -/

/-- The source presheaf `(∅, {1}, ∅ → {1})` of the witness morphism. -/
@[implicit_reducible]
def srcPresheaf : Presheaf where
  obj a := match a with | ⟨X⟩ => PEmpty | ⟨U⟩ => PUnit
  map {a b} h :=
    match a, b, h with
    | ⟨_⟩, ⟨_⟩, ⟨idX⟩ => TypeCat.ofHom (fun (x : PEmpty) => x)
    | ⟨_⟩, ⟨_⟩, ⟨idU⟩ => TypeCat.ofHom (fun (x : PUnit) => x)
    | ⟨_⟩, ⟨_⟩, ⟨f⟩ => TypeCat.ofHom (fun (x : PEmpty) => x.elim)
  map_id := by rintro ⟨⟨⟩⟩ <;> rfl
  map_comp := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨⟨⟩⟩ ⟨⟨⟩⟩ <;> rfl

/-- The target presheaf `({1}, {1}, id_{1})` of the witness morphism. -/
@[implicit_reducible]
def tgtPresheaf : Presheaf where
  obj _ := PUnit
  map _ := TypeCat.ofHom (id : PUnit → PUnit)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The witness morphism `(∅, {1}, ∅→{1}) ⟶ ({1}, {1}, id)`. -/
@[implicit_reducible]
def witness : srcPresheaf ⟶ tgtPresheaf where
  app a := match a with
    | ⟨X⟩ => TypeCat.ofHom (fun (x : PEmpty) => (x.elim : PUnit))
    | ⟨U⟩ => TypeCat.ofHom (fun (_ : PUnit) => PUnit.unit)
  naturality := by rintro ⟨a⟩ ⟨b⟩ ⟨⟨⟩⟩ <;> rfl

/-- Both components of the witness are injective, so it is a monomorphism. -/
theorem witness_mono : Mono witness := by
  rw [NatTrans.mono_iff_mono_app]
  intro k
  rw [CategoryTheory.mono_iff_injective]
  obtain ⟨(_ | _)⟩ := k
  · exact fun x => x.elim
  · intro a b _
    rfl

/-- The induced map on the source pushout has distinct images on the two
inclusions of `PUnit.unit` (no gluing, since `A = ∅`). -/
theorem pushout_src_inl_ne_inr :
    PushoutObj.inl srcPresheaf PUnit.unit ≠ PushoutObj.inr srcPresheaf PUnit.unit := by
  let g : PushoutObj srcPresheaf → Bool :=
    Quot.lift (fun x => match x with | Sum.inl _ => true | Sum.inr _ => false)
      (by rintro _ _ ⟨a⟩; exact a.elim)
  intro h
  have : g (PushoutObj.inl srcPresheaf PUnit.unit) =
      g (PushoutObj.inr srcPresheaf PUnit.unit) := by rw [h]
  simp only [g, PushoutObj.inl, PushoutObj.inr] at this
  exact Bool.noConfusion this

/-- The induced pushout map of `witness` is not injective. -/
theorem pushout_map_witness_not_injective :
    ¬ Function.Injective (PushoutObj.map witness) := by
  intro hinj
  have heq : PushoutObj.map witness (PushoutObj.inl srcPresheaf PUnit.unit) =
      PushoutObj.map witness (PushoutObj.inr srcPresheaf PUnit.unit) := by
    rw [PushoutObj.map_inl, PushoutObj.map_inr]
    have hg : PushoutObj.inl tgtPresheaf (witness.app (Opposite.op U) PUnit.unit) =
        PushoutObj.inr tgtPresheaf (restr tgtPresheaf PUnit.unit) :=
      Quot.sound (PushoutRel.glue (ℱ := tgtPresheaf) PUnit.unit)
    rw [hg]
    rfl
  exact pushout_src_inl_ne_inr (hinj heq)

/-- **Statement 2 (pushout form).** The pushout functor does not preserve monos. -/
theorem pushoutFunctor_not_preservesMono :
    ¬ pushoutFunctor.PreservesMonomorphisms := by
  intro h
  have := witness_mono
  have hmono : Mono (pushoutFunctor.map witness) := h.preserves (f := witness)
  rw [CategoryTheory.mono_iff_injective] at hmono
  exact pushout_map_witness_not_injective hmono

/-- **Statement 2.** The site-theoretic stalk functor is not left exact. -/
theorem stalkFunctor_not_preservesMono :
    ¬ stalkFunctor.PreservesMonomorphisms := by
  intro h
  obtain ⟨e⟩ := stalkIsoPushout
  exact pushoutFunctor_not_preservesMono ((Functor.PreservesMonomorphisms.iso_iff e).mp h)

/-! ## Statement 3: consequence — `u` is not a point. -/

/-- **Statement 3.** Because the stalk functor `ℱ ↦ ℱ_p` fails to preserve
monomorphisms (Statement 2), it fails to be left exact. -/
@[stacks 00YD]
theorem u_not_point : ¬ PreservesFiniteLimits stalkFunctor := by
  intro h
  exact stalkFunctor_not_preservesMono
    (preservesMonomorphisms_of_preservesLimitsOfShape stalkFunctor)

end Counterexample
