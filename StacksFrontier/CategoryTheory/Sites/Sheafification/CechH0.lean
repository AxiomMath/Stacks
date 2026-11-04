module

public import StacksFrontier.CategoryTheory.Sites.Hypercover.ZeroOver
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Zeroth Čech cohomology of a family of morphisms with fixed target

For a presheaf of sets `F` and a family of morphisms with fixed target `𝒰 = {U_i ⟶ U}` —
Mathlib's `CategoryTheory.PreZeroHypercover U` — `H⁰(𝒰, F)` is the set of families of sections
`s_i ∈ F(U_i)` that agree where their sources meet. A morphism of families pulls sections back,
and this pullback depends only on the induced morphism of targets (Stacks 00W7). Hence
(Stacks 00W8) if `𝒰` and `𝒱` refine each other, the two pullbacks are mutually inverse
bijections, giving an identification `H⁰(𝒰, F) ≃ H⁰(𝒱, F)` independent of the chosen
refinements.

## `IsMatching` quantifies over cones, so no fibre products are needed anywhere

The source defines `H⁰` by the equalizer diagram of 00VN, whose middle term is indexed by the
fibre products `U_i ×_U U_{i'}`; a formalization following that literally must assume those
pullbacks exist and carry `[∀ i i', HasPullback (𝒰.f i) (𝒰.f i')]` on every declaration.
`IsMatching` instead asks for agreement on *every* cone over each pair `(U_i, U_{i'})`, which
needs no limits at all.

The two agree wherever the source's version is defined: `isMatching_iff_isCompatible` proves
`IsMatching ↔ IsCompatible` under `[∀ i j, HasPullback (𝒰.f i) (𝒰.f j)]`. Forwards, instantiate
at the fibre product itself; backwards, every cone factors through it via `pullback.lift`. So
this is the source's `H⁰` where the source's definition applies, and is defined more widely.

## 00W7 is stated sharper here than in the source

`PreZeroHypercover.HomOver E G g` carries the base morphism `g` as a *parameter*, not a field.
So "two morphisms of families inducing the same morphism `U → V`" is simply "two elements of
`E.HomOver G g`", and 00W7 needs no hypothesis relating two base morphisms: it says the induced
map on `H⁰` is determined by `g` alone.
-/

@[expose] public section

namespace CategoryTheory.PreZeroHypercover

open Opposite Limits

universe w w' w'' t v u

variable {C : Type u} [Category.{v} C] {U V W : C} (F : Cᵒᵖ ⥤ Type t)

/-! ### Matching families -/

/-- **Stacks 00VN / 00W1**, the matching condition. A family of sections `s_i ∈ F(U_i)` over
`𝒰 = {U_i ⟶ U}` is *matching* if for every pair of indices and every cone `T` over their
sources commuting over `U`, the two restrictions of `s_i` and `s_j` to `T` agree.

No fibre products are required. Where they exist this is the source's condition —
see `isMatching_iff_isCompatible`. -/
def IsMatching (E : PreZeroHypercover.{w} U) (s : ∀ i, F.obj (op (E.X i))) : Prop :=
  ∀ i j (T : C) (a : T ⟶ E.X i) (b : T ⟶ E.X j),
    a ≫ E.f i = b ≫ E.f j → F.map a.op (s i) = F.map b.op (s j)

/-- The source's form of the matching condition, on the fibre products `U_i ×_U U_j` that the
equalizer diagram of 00VN is written with. -/
def IsCompatible (E : PreZeroHypercover.{w} U) [∀ i j, HasPullback (E.f i) (E.f j)]
    (s : ∀ i, F.obj (op (E.X i))) : Prop :=
  ∀ i j, F.map (pullback.fst (E.f i) (E.f j)).op (s i)
       = F.map (pullback.snd (E.f i) (E.f j)).op (s j)

/-- The pullback-free matching condition agrees with agreement on any *exhibited* family of
fibre products.

This is the form the fibre products are usually available in: a site in the Stacks sense
supplies a chosen `U_i ×_X U_j` with a pullback witness for each pair, rather than a
`HasPullback` instance for every pair of morphisms of the ambient category. Forwards,
instantiate `IsMatching` at the exhibited cone, whose commutativity is `IsPullback.w`.
Backwards, an arbitrary commuting cone `(T, a, b)` factors through the exhibited one via
`IsPullback.lift`, and pulling the agreement of `s` back along that lift gives the equality. -/
lemma isMatching_iff_of_isPullback (E : PreZeroHypercover.{w} U)
    (P : E.I₀ → E.I₀ → C) (fst : ∀ i j, P i j ⟶ E.X i) (snd : ∀ i j, P i j ⟶ E.X j)
    (hP : ∀ i j, IsPullback (fst i j) (snd i j) (E.f i) (E.f j))
    (s : ∀ i, F.obj (op (E.X i))) :
    IsMatching F E s ↔ ∀ i j, F.map (fst i j).op (s i) = F.map (snd i j).op (s j) := by
  refine ⟨fun h i j => h i j _ _ _ (hP i j).w, fun h i j T a b hab => ?_⟩
  have := congrArg (F.map ((hP i j).lift a b hab).op) (h i j)
  simpa only [← Functor.map_comp_apply, ← op_comp, (hP i j).lift_fst, (hP i j).lift_snd] using this

/-- The pullback-free matching condition agrees with the source's fibre-product condition
wherever the latter is defined. This is `isMatching_iff_of_isPullback` at Mathlib's chosen
pullbacks. -/
lemma isMatching_iff_isCompatible (E : PreZeroHypercover.{w} U)
    [∀ i j, HasPullback (E.f i) (E.f j)] (s : ∀ i, F.obj (op (E.X i))) :
    IsMatching F E s ↔ IsCompatible F E s :=
  isMatching_iff_of_isPullback F E _ _ _ (fun _ _ => IsPullback.of_hasPullback _ _) s

/-- **Stacks 00W1.** The zeroth Čech cohomology `H⁰(𝒰, F)`: the matching families of sections.
-/
def H0 (E : PreZeroHypercover.{w} U) : Type _ := { s : ∀ i, F.obj (op (E.X i)) // IsMatching F E s }

/-- Two elements of `H⁰(𝒰, F)` agreeing in every section are equal, since being matching is a
proposition. -/
@[ext]
lemma H0.ext {E : PreZeroHypercover.{w} U} {s t : H0 F E} (h : ∀ i, s.1 i = t.1 i) : s = t :=
  Subtype.ext (funext h)

/-! ### Pullback along a morphism of families -/

/-- Pullback of sections along a morphism of families with fixed target:
`(φ^* s)_i = F(φ.h₀ i)(s_{φ.s₀ i})`.

That this again matches uses only `φ.w₀` and the matching property of `s` at a shifted cone —
no fibre products. -/
def H0.mapOver {E : PreZeroHypercover.{w} U} {G : PreZeroHypercover.{w'} V} {g : U ⟶ V}
    (φ : E.HomOver G g) (s : H0 F G) : H0 F E :=
  ⟨fun i => F.map (φ.h₀ i).op (s.1 (φ.s₀ i)), by
    intro i j T a b hab
    simp only [← Functor.map_comp_apply, ← op_comp]
    refine s.2 _ _ T (a ≫ φ.h₀ i) (b ≫ φ.h₀ j) ?_
    rw [Category.assoc, φ.w₀, ← Category.assoc, hab, Category.assoc, ← φ.w₀, Category.assoc]⟩

/-- The `i`-th section of `φ^* s` is `F(φ.h₀ i)(s_{φ.s₀ i})`. -/
@[simp]
lemma H0.mapOver_apply {E : PreZeroHypercover.{w} U} {G : PreZeroHypercover.{w'} V} {g : U ⟶ V}
    (φ : E.HomOver G g) (s : H0 F G) (i : E.I₀) :
    (H0.mapOver F φ s).1 i = F.map (φ.h₀ i).op (s.1 (φ.s₀ i)) :=
  rfl

/-- The identity morphism of families induces the identity on `H⁰`. -/
@[simp]
lemma H0.mapOver_id (E : PreZeroHypercover.{w} U) (s : H0 F E) :
    H0.mapOver F (HomOver.id E) s = s := by
  refine H0.ext F fun i => ?_
  simp only [H0.mapOver, HomOver.id, op_id, F.map_id]
  rfl

/-- Pullback is contravariantly functorial in the morphism of families. -/
lemma H0.mapOver_comp {E : PreZeroHypercover.{w} U} {G : PreZeroHypercover.{w'} V}
    {H : PreZeroHypercover.{w''} W} {g : U ⟶ V} {h : V ⟶ W} {k : U ⟶ W}
    (φ : E.HomOver G g) (ψ : G.HomOver H h) (hk : g ≫ h = k) (s : H0 F H) :
    H0.mapOver F (φ.comp ψ hk) s = H0.mapOver F φ (H0.mapOver F ψ s) := by
  refine H0.ext F fun i => ?_
  simp only [H0.mapOver, HomOver.comp, ← Functor.map_comp_apply, ← op_comp]
  rfl

/-! ### Stacks 00W7 and 00W8 -/

/-- **Stacks 00W7.** Any two morphisms of families `𝒰 → 𝒱` inducing the same morphism of
targets induce the same map `H⁰(𝒱, F) → H⁰(𝒰, F)`.

Because `HomOver` carries the base morphism as a parameter, "inducing the same morphism of
targets" is expressed by the two morphisms having the same type, and the statement is that the
induced map depends on `g` alone. The proof applies the matching property of `s` at the single
cone `(U_i, φ.h₀ i, ψ.h₀ i)`, which commutes over `V` precisely because both morphisms lie
over `g`. -/
@[stacks 00W7]
theorem H0.mapOver_eq_of_homOver {E : PreZeroHypercover.{w} U} {G : PreZeroHypercover.{w'} V}
    {g : U ⟶ V} (φ ψ : E.HomOver G g) : H0.mapOver F φ = H0.mapOver F ψ :=
  funext fun s => H0.ext F fun i =>
    s.2 (φ.s₀ i) (ψ.s₀ i) (E.X i) (φ.h₀ i) (ψ.h₀ i) (by rw [φ.w₀, ψ.w₀])

/-- Mutual refinements induce mutually inverse maps on `H⁰`. This is the content of Stacks 00W8,
and the whole argument is 00W7 applied to the composite: `φ.comp ψ (Category.comp_id _)` is a
morphism `𝒰 → 𝒰` over `𝟙 U`, hence induces the same map as `HomOver.id`, which is the
identity. -/
lemma H0.mapOver_mapOver {E G : PreZeroHypercover.{w} U}
    (φ : E.HomOver G (𝟙 U)) (ψ : G.HomOver E (𝟙 U)) (s : H0 F E) :
    H0.mapOver F φ (H0.mapOver F ψ s) = s := by
  rw [← H0.mapOver_comp F φ ψ (Category.comp_id _),
    H0.mapOver_eq_of_homOver F (φ.comp ψ (Category.comp_id _)) (HomOver.id E),
    H0.mapOver_id]

/-- **Stacks 00W8.** If `𝒰` refines `𝒱` and `𝒱` refines `𝒰`, the two induced pullback maps on
`H⁰` are mutually inverse bijections, so there is a canonical identification
`H⁰(𝒰, F) = H⁰(𝒱, F)`. -/
@[stacks 00W8]
theorem H0.mapOver_bijective_of_mutual_refinement {E G : PreZeroHypercover.{w} U}
    (φ : E.HomOver G (𝟙 U)) (ψ : G.HomOver E (𝟙 U)) :
    (∀ s : H0 F E, H0.mapOver F φ (H0.mapOver F ψ s) = s) ∧
      (∀ t : H0 F G, H0.mapOver F ψ (H0.mapOver F φ t) = t) :=
  ⟨H0.mapOver_mapOver F φ ψ, H0.mapOver_mapOver F ψ φ⟩

/-- **Stacks 00W8**, packaged as the bijection `H⁰(𝒱, F) ≃ H⁰(𝒰, F)` determined by mutual
refinements. By 00W7 it does not depend on which refinements are chosen. -/
@[stacks 00W8]
def H0.refinementEquiv {E G : PreZeroHypercover.{w} U}
    (φ : E.HomOver G (𝟙 U)) (ψ : G.HomOver E (𝟙 U)) : H0 F G ≃ H0 F E where
  toFun := H0.mapOver F φ
  invFun := H0.mapOver F ψ
  left_inv := H0.mapOver_mapOver F ψ φ
  right_inv := H0.mapOver_mapOver F φ ψ

/-- **Stacks 00W8**, the independence clause: the identification above is canonical, since any
two refinements `𝒰 → 𝒱` induce the same map. This is 00W7 at `g = 𝟙 U`. -/
@[stacks 00W8, sga "3 IV 1.12" "Clause, special case"]
theorem H0.refinementEquiv_eq {E G : PreZeroHypercover.{w} U}
    (φ φ' : E.HomOver G (𝟙 U)) (ψ ψ' : G.HomOver E (𝟙 U)) :
    H0.refinementEquiv F φ ψ = H0.refinementEquiv F φ' ψ' :=
  Equiv.coe_inj.mp (H0.mapOver_eq_of_homOver F φ φ')

end CategoryTheory.PreZeroHypercover
