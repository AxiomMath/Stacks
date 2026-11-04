module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.GroupTheory.FreeAbelianGroup

/-! # The Grothendieck group of a category: Stacks 02MU, 02MV

Stacks 02MU: the *zeroth K-group* `K₀(𝒜)` of an abelian category `𝒜` is the free abelian group
on the objects of `𝒜` modulo the relations `[B] - [A] - [C] = 0`, one for every short exact
sequence `0 → A → B → C → 0`. Stacks 02MV: an exact functor `F : 𝒜 ⥤ ℬ` between abelian
categories induces a homomorphism `K₀(F) : K₀(𝒜) → K₀(ℬ)`, `[A] ↦ [F(A)]`.

Besides these, the file develops the basic API: when two classes are equal (`mk_eq_mk_iff`,
`of_eq_of_iff`), induction and extensionality on the classes of objects
(`GrothendieckGroup.induction`, `hom_ext`), the classes of zero objects, of isomorphic objects and
of biproducts, and the functoriality of `map`. `map_surjective` proves the surjectivity in Stacks
02MX (1) for any essentially surjective `F` into a category with a zero object, such as the
quotient functor `𝒜 ⥤ 𝒜/𝒞` by a Serre subcategory `𝒞`.

## Design

* `GrothendieckGroup C` is defined for any category with zero morphisms, the weakest setting in
  which `ShortComplex.ShortExact` makes sense; the abelian case is Stacks'.
* The generators are the objects themselves, as in Stacks, not isomorphism classes, so no
  smallness assumption is needed and `GrothendieckGroup C` lives in the universe of the objects.
  Isomorphic objects have equal classes once `C` has a zero object.
* `GrothendieckGroup C` is a `def` for the quotient of `FreeAbelianGroup C` by the closure of
  `GrothendieckGroup.relations C`, with a derived `AddCommGroup` instance, like Mathlib's
  `PresentedGroup`. Apart from that instance, the section `Quotient` below is the only place that
  uses the fact that it is a quotient. It gives `GrothendieckGroup C` an interface in the style of
  `QuotientAddGroup`: the projection `mk : FreeAbelianGroup C →+ GrothendieckGroup C`, bundled
  like `QuotientAddGroup.mk'` and `PresentedGroup.mk`, with `mk_surjective` and `mk_eq_zero_iff`
  (the kernel of `mk` is the closure of the relations), and the universal property `lift` with
  `lift_mk`. Everything after the section, starting with `induction_on`, uses this interface
  alone: it still compiles with `attribute [local irreducible] GrothendieckGroup mk lift`
  inserted right after the section.
* `mk_eq_zero_iff` is not `@[simp]` (unlike `QuotientAddGroup.eq_zero_iff`, like
  `PresentedGroup.mk_eq_one_iff`), so that `simp` never turns `of X = 0` into a statement about
  the closure of the relations.
* `GrothendieckGroup` is `@[implicit_reducible]`, which lets the bodies of `mk` and `lift`
  typecheck at implicit transparency; nothing needs it to compile or to pass the transparency
  linter. Through `deriving` it also applies to the data fields of the instance. It stays in
  force in later files, where code that crosses to the quotient (for example with
  `QuotientAddGroup.induction_on`) typechecks with no error and no linter warning, so keeping to
  the interface there is a convention that Lean does not check.
* `of X` is an `abbrev` for `mk (FreeAbelianGroup.of X)`, so the lemmas about `mk` apply to the
  classes of objects with no unfolding lemma.
* `GrothendieckGroup.map` (02MV) is stated for any functor preserving zero morphisms and sending
  short exact sequences to short exact sequences; an exact functor between abelian categories
  supplies the hypothesis via `ShortComplex.ShortExact.map_of_exact`.
* The names `relations`, `of`, `additivity`, `of_biprod`, `of_eq_zero_of_isZero`, `of_zero` and
  `of_eq_of_iso` follow Joël Riou's `CategoryTheory.ExactCategory.GrothendieckGroup` (draft
  Mathlib PR #25848). There the relation is `[S.X₁] + [S.X₃] - [S.X₂]`, which generates the same
  subgroup, and `S` in `relations.ofShortExact` and `additivity`, `X` in `of_eq_zero_of_isZero`
  and `C` in `of_zero` are explicit.
* Mathlib's unrelated `Algebra.GrothendieckGroup`, the group completion of a commutative monoid,
  shares the last component of the name and of `of` and `lift`: in a file that opens both
  `Algebra` and `CategoryTheory`, write `CategoryTheory.GrothendieckGroup` where a use is
  ambiguous.
-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory

open Limits ZeroObject

variable (C : Type u) [Category.{v} C] [HasZeroMorphisms C]

/-- The relations `[S.X₂] - [S.X₁] - [S.X₃]` in the free abelian group on the objects of `C`,
one for each short exact sequence `S`. -/
inductive GrothendieckGroup.relations : Set (FreeAbelianGroup C)
  /-- The relation `[S.X₂] - [S.X₁] - [S.X₃]` of a short exact sequence `S`. -/
  | ofShortExact {S : ShortComplex C} (hS : S.ShortExact) :
      relations (.of S.X₂ - .of S.X₁ - .of S.X₃)

/-- The Grothendieck group `K₀(C)`: the free abelian group on the objects of `C` modulo
`[S.X₂] = [S.X₁] + [S.X₃]` for every short exact sequence `S`. -/
@[implicit_reducible, stacks 02MU "free on the objects; for any category with zero morphisms"]
def GrothendieckGroup : Type u :=
  FreeAbelianGroup C ⧸ AddSubgroup.closure (GrothendieckGroup.relations C)
deriving AddCommGroup

namespace GrothendieckGroup

variable {C} {G : Type w} [AddCommGroup G]

/-! ### The quotient interface

Together with the derived `AddCommGroup` instance, the declarations of this section are the only
ones that use the fact that `GrothendieckGroup C` is the quotient of `FreeAbelianGroup C` by the
subgroup generated by the relations. Everything after the section goes through them. -/

section Quotient

/-- The projection from the free abelian group on the objects of `C` onto `K₀(C)`, sending a
formal sum of objects to its class. -/
def mk : FreeAbelianGroup C →+ GrothendieckGroup C :=
  QuotientAddGroup.mk' _

/-- Every element of `K₀(C)` is the class of a formal sum of objects. -/
lemma mk_surjective : Function.Surjective (mk (C := C)) :=
  QuotientAddGroup.mk'_surjective _

/-- The kernel of `mk` is the subgroup generated by the relations: `mk x = 0` if and only if `x`
lies in it. -/
lemma mk_eq_zero_iff {x : FreeAbelianGroup C} :
    mk x = 0 ↔ x ∈ AddSubgroup.closure (relations C) :=
  QuotientAddGroup.eq_zero_iff x

/-- The universal property: a function on objects that is additive on short exact sequences
induces a homomorphism out of `K₀(C)`. -/
def lift (f : C → G) (hf : ∀ ⦃S : ShortComplex C⦄, S.ShortExact → f S.X₂ = f S.X₁ + f S.X₃) :
    GrothendieckGroup C →+ G :=
  QuotientAddGroup.lift _ (FreeAbelianGroup.lift f) <| (AddSubgroup.closure_le _).2 <| by
    rw [Set.subset_def]
    intro x hx
    cases hx with | ofShortExact hS => simp [hf hS]

/-- `lift f hf` sends the class of a formal sum of objects `x` to `FreeAbelianGroup.lift f x`. -/
@[simp]
lemma lift_mk {f : C → G}
    (hf : ∀ ⦃S : ShortComplex C⦄, S.ShortExact → f S.X₂ = f S.X₁ + f S.X₃)
    (x : FreeAbelianGroup C) : lift f hf (mk x) = FreeAbelianGroup.lift f x :=
  rfl

end Quotient

instance : Inhabited (GrothendieckGroup C) := ⟨0⟩

/-- Induction on `mk`: a statement holds for every element of `K₀(C)` once it holds for the
class of every formal sum of objects. -/
@[elab_as_elim]
lemma induction_on {motive : GrothendieckGroup C → Prop} (x : GrothendieckGroup C)
    (H : ∀ z, motive (mk z)) : motive x := by
  obtain ⟨z, rfl⟩ := mk_surjective x
  exact H z

/-- The class `[X]` of an object `X` in `K₀(C)`. -/
abbrev of (X : C) : GrothendieckGroup C := mk (FreeAbelianGroup.of X)

/-- The class of the middle term of a short exact sequence is the sum of the other two. -/
@[stacks 02MU "the relation `[B] = [A] + [C]` of a short exact sequence"]
lemma additivity {S : ShortComplex C} (hS : S.ShortExact) : of S.X₂ = of S.X₁ + of S.X₃ := by
  have h := mk_eq_zero_iff.2 (AddSubgroup.mem_closure_of_mem (relations.ofShortExact hS))
  rwa [map_sub, map_sub, sub_sub, sub_eq_zero] at h

variable {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]

/-- The homomorphism `K₀(F) : K₀(C) → K₀(D)`, `[X] ↦ [F(X)]`, induced by a functor preserving
zero morphisms and short exact sequences. -/
@[stacks 02MV "for any functor preserving zero morphisms and short exact sequences"]
def map (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (hF : ∀ ⦃S : ShortComplex C⦄, S.ShortExact → (S.map F).ShortExact) :
    GrothendieckGroup C →+ GrothendieckGroup D :=
  lift (fun X ↦ of (F.obj X)) fun _ hS ↦ additivity (hF hS)

/-- Two formal sums of objects have the same class if and only if their difference lies in the
subgroup generated by the relations. -/
lemma mk_eq_mk_iff {x y : FreeAbelianGroup C} :
    mk x = mk y ↔ x - y ∈ AddSubgroup.closure (relations C) := by
  rw [← sub_eq_zero, ← map_sub, mk_eq_zero_iff]

/-- Two objects have the same class if and only if the difference of the corresponding
generators lies in the subgroup generated by the relations. -/
lemma of_eq_of_iff {X Y : C} :
    of X = of Y ↔ FreeAbelianGroup.of X - FreeAbelianGroup.of Y ∈
      AddSubgroup.closure (relations C) :=
  mk_eq_mk_iff

/-- `lift f hf` sends the class of an object `X` to `f X`. This is not a `simp` lemma: `simp`
proves it from `lift_mk` and `FreeAbelianGroup.lift_apply_of`, since `of X` is
`mk (FreeAbelianGroup.of X)`. -/
lemma lift_of {f : C → G}
    (hf : ∀ ⦃S : ShortComplex C⦄, S.ShortExact → f S.X₂ = f S.X₁ + f S.X₃) (X : C) :
    lift f hf (of X) = f X := by
  rw [lift_mk, FreeAbelianGroup.lift_apply_of]

/-- Induction on the classes of objects, in the shape of `FreeAbelianGroup.induction_on`: a
property holds for every element of `K₀(C)` once it holds for `0` and for the class of every
object, for `-[X]` whenever it holds for `[X]`, and for `x + y` whenever it holds for `x` and
`y`. It is the default eliminator of the `induction` tactic on `K₀(C)`: `induction x with` has
the cases `zero`, `of`, `neg` and `add`. -/
@[elab_as_elim, induction_eliminator]
protected lemma induction {motive : GrothendieckGroup C → Prop} (x : GrothendieckGroup C)
    (zero : motive 0) (of : ∀ X, motive (of X)) (neg : ∀ X, motive (.of X) → motive (-.of X))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive x := by
  induction x using induction_on with | H z => ?_
  induction z using FreeAbelianGroup.induction_on with
  | zero => rw [map_zero]; exact zero
  | of X => exact of X
  | neg X h => rw [map_neg]; exact neg X h
  | add x y hx hy => rw [map_add]; exact add _ _ hx hy

/-- Two homomorphisms from `K₀(C)` to an additive monoid are equal once they agree on the class
of every object. -/
@[ext]
lemma hom_ext {M : Type*} [AddMonoid M] {φ ψ : GrothendieckGroup C →+ M}
    (h : ∀ X, φ (of X) = ψ (of X)) : φ = ψ := by
  refine AddMonoidHom.ext fun x ↦ ?_
  induction x with
  | zero => rw [map_zero, map_zero]
  | of X => exact h X
  | neg X _ => exact eq_on_neg φ ψ (h X)
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- A zero object has class `0`. -/
lemma of_eq_zero_of_isZero {X : C} (hX : IsZero X) : of X = 0 := by
  have hS : (ShortComplex.mk (𝟙 X) (𝟙 X) (hX.eq_of_src _ _)).ShortExact :=
    { exact := ShortComplex.exact_of_isZero_X₂ _ hX }
  have := additivity hS
  rwa [left_eq_add] at this

/-- The class of the zero object is `0`. -/
@[simp]
lemma of_zero [HasZeroObject C] : of (0 : C) = 0 :=
  of_eq_zero_of_isZero (isZero_zero C)

/-- In a category with a zero object, isomorphic objects have the same class. -/
lemma of_eq_of_iso [HasZeroObject C] {X Y : C} (e : X ≅ Y) : of X = of Y := by
  let S := ShortComplex.mk e.hom (0 : Y ⟶ 0) comp_zero
  have hS : S.ShortExact :=
    { exact := by
        rw [(ShortComplex.HomologyData.ofIsColimitCokernelCofork S rfl _
          (CokernelCofork.IsColimit.ofEpiOfIsZero (CokernelCofork.ofπ (0 : S.X₂ ⟶ 0) comp_zero)
            inferInstance (isZero_zero C))).exact_iff]
        simpa using isZero_zero C
      epi_g := (isZero_zero C).epi _ }
  simpa [S] using (additivity hS).symm

/-- The class of a binary biproduct is the sum of the classes of the two factors. -/
@[simp]
lemma of_biprod {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    (X Y : C) [HasBinaryBiproduct X Y] : of (X ⊞ Y) = of X + of Y :=
  additivity (ShortComplex.Splitting.ofHasBinaryBiproduct X Y).shortExact

/-- With binary biproducts, every element of `K₀(C)` is a difference `[X] - [Y]` of the classes
of two objects. -/
lemma exists_eq_of_sub_of {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] (x : GrothendieckGroup C) : ∃ X Y : C, x = of X - of Y := by
  induction x with
  | zero => exact ⟨0, 0, by simp⟩
  | of X => exact ⟨X, 0, by simp⟩
  | neg X _ => exact ⟨0, X, by simp⟩
  | add x y hx hy =>
    obtain ⟨X, Y, rfl⟩ := hx
    obtain ⟨X', Y', rfl⟩ := hy
    exact ⟨X ⊞ X', Y ⊞ Y', by rw [of_biprod, of_biprod]; abel⟩

section map

variable {E : Type*} [Category* E] [HasZeroMorphisms E]

/-- `K₀(F)` sends the class of `X` to the class of `F(X)`. -/
@[simp, stacks 02MV "`K₀(F)[A] = [F(A)]`"]
lemma map_of (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (hF : ∀ ⦃S : ShortComplex C⦄, S.ShortExact → (S.map F).ShortExact) (X : C) :
    map F hF (of X) = of (F.obj X) := by
  rw [map, lift_of]

/-- `K₀` of the identity functor is the identity. -/
@[simp]
lemma map_id : map (𝟭 C) (fun _ hS ↦ hS) = AddMonoidHom.id _ := by
  ext X
  simp

/-- `K₀` of a composite of two functors is the composite of their maps on `K₀`. -/
lemma map_comp (F : C ⥤ D) (G : D ⥤ E) [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (hF : ∀ ⦃S : ShortComplex C⦄, S.ShortExact → (S.map F).ShortExact)
    (hG : ∀ ⦃S : ShortComplex D⦄, S.ShortExact → (S.map G).ShortExact) :
    map (F ⋙ G) (fun _ hS ↦ hG (hF hS)) = (map G hG).comp (map F hF) := by
  ext X
  simp

/-- Two functors into a category with a zero object whose values on each object are isomorphic
induce the same map on `K₀`; no naturality is needed. For a natural isomorphism, see
`map_eq_of_iso`. -/
lemma map_congr [HasZeroObject D] {F G : C ⥤ D} [F.PreservesZeroMorphisms]
    [G.PreservesZeroMorphisms] (e : ∀ X, F.obj X ≅ G.obj X)
    (hF : ∀ ⦃S : ShortComplex C⦄, S.ShortExact → (S.map F).ShortExact)
    (hG : ∀ ⦃S : ShortComplex C⦄, S.ShortExact → (S.map G).ShortExact) :
    map F hF = map G hG := by
  ext X
  simpa using of_eq_of_iso (e X)

/-- Naturally isomorphic functors into a category with a zero object induce the same map on
`K₀`. -/
lemma map_eq_of_iso [HasZeroObject D] {F G : C ⥤ D} [F.PreservesZeroMorphisms]
    [G.PreservesZeroMorphisms] (e : F ≅ G)
    (hF : ∀ ⦃S : ShortComplex C⦄, S.ShortExact → (S.map F).ShortExact)
    (hG : ∀ ⦃S : ShortComplex C⦄, S.ShortExact → (S.map G).ShortExact) :
    map F hF = map G hG :=
  map_congr e.app hF hG

/-- An essentially surjective functor into a category with a zero object induces a surjection on
`K₀`. For the quotient functor `𝒜 ⥤ 𝒜/𝒞` by a Serre subcategory `𝒞` this is the surjectivity of
`K₀(𝒜) → K₀(𝒜/𝒞)` in Stacks 02MX (1). -/
@[stacks 02MX "(1), surjectivity, for any essentially surjective `F` to a category with `0`"]
lemma map_surjective [HasZeroObject D] (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.EssSurj]
    (hF : ∀ ⦃S : ShortComplex C⦄, S.ShortExact → (S.map F).ShortExact) :
    Function.Surjective (map F hF) := by
  intro y
  induction y with
  | zero => exact ⟨0, map_zero _⟩
  | of Y => exact ⟨of (F.objPreimage Y), by simpa using of_eq_of_iso (F.objObjPreimageIso Y)⟩
  | neg Y hY =>
    obtain ⟨x, hx⟩ := hY
    exact ⟨-x, by rw [map_neg, hx]⟩
  | add x y hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, map_add _ _ _⟩

end map

end GrothendieckGroup

end CategoryTheory
