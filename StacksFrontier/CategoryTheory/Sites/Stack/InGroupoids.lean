module

public import StacksFrontier.CategoryTheory.Sites.Stack.GroupoidTFAE
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge
public import StacksFrontier.CategoryTheory.Sites.Gerbe.WhenGerbe
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks in groupoids, and gerbes over a stack in groupoids

Let `(𝒞, J)` be a site. A *stack in groupoids* over `𝒞` (Stacks 02ZI) is a category
`p : 𝒮 ⥤ 𝒞` over `𝒞` which is fibred in groupoids, whose presheaves `Isom(x, y)` on `𝒞/U` are
sheaves, and relative to which every descent datum for a covering is effective. Given stacks in
groupoids `F ⋙ q : 𝒳 ⥤ 𝒞` and `q : 𝒴 ⥤ 𝒞` and a `1`-morphism `F : 𝒳 ⥤ 𝒴` over `𝒞`, `𝒳` is a
*gerbe over* `𝒴` (Stacks 06P2) when the equivalent conditions of Stacks 06P1 hold.

## Main definitions

* `CategoryTheory.Functor.IsStackInGroupoidsBySieves`: Stacks 02ZI, stated with covering sieves
  and with the presheaves `Isom(x, y)` of Stacks 02ZB, in the language in which
  `CategoryTheory.Functor.IsStack` states Stacks 026F.
* `CategoryTheory.IsGerbeOverStackInGroupoids`: Stacks 06P2.

## Main results

* `CategoryTheory.Functor.isStackInGroupoidsBySieves_iff`: a stack in groupoids is exactly a
  category fibred in groupoids which is a stack (Stacks 02ZJ).
* `CategoryTheory.Functor.IsStackInGroupoidsBySieves.isStackInGroupoids`: it satisfies the
  covering-family conditions `CategoryTheory.Functor.IsStackInGroupoids`.
* `CategoryTheory.isGerbeOverStackInGroupoids_iff_isGerbe_of_factorization`: for stacks in
  groupoids, Stacks 06P2 is condition (1) of Stacks 06P1 at any factorization `F = a ⋙ F'`.

## Implementation notes

`CategoryTheory.Functor.IsStackInGroupoids` renders the conditions of Stacks 02ZI with covering
*families* together with supplied fibre products `Vᵢ ×_U Vⱼ` and `Vᵢ ×_U Vⱼ ×_U Vₖ`; over a base
in which those fibre products need not exist (Mathlib's `GrothendieckTopology` does not ask for
them, while the sites of the source have them by Sites, Definition 00VH (3)) its conditions (2)
and (3) can hold with nothing to prove. `IsStackInGroupoidsBySieves` states (2) and (3) with
covering *sieves*, as `CategoryTheory.Functor.IsStack` does for Stacks 026F, and so has no such
gap; it implies `IsStackInGroupoids` at every index universe.

A `1`-morphism of categories over `𝒞` from `p : 𝒳 ⥤ 𝒞` to `q : 𝒴 ⥤ 𝒞` is a functor
`F : 𝒳 ⥤ 𝒴` with `F ⋙ q = p`, so the structure functor of `𝒳` is `F ⋙ q`.
-/

@[expose] public section

namespace CategoryTheory

universe w v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace Functor

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]

/-- **Stacks 02ZI.** A category `p : 𝒮 ⥤ 𝒞` over the site `(𝒞, J)` is a *stack in groupoids* if
1. `p` is fibred in groupoids over `𝒞`;
2. for all `U` of `𝒞` and all `x`, `y` of the fibre `𝒮_U`, the presheaf `Isom(x, y)` of
   Stacks 02ZB (`CategoryTheory.Functor.isomPresheaf`) is a sheaf on the site `𝒞/U`;
3. every descent datum relative to a covering of `U` is effective
   (`CategoryTheory.Functor.HasEffectiveDescent`).

Conditions (2) and (3) are stated with the chosen pullbacks of the fibred structure that
condition (1) provides. -/
@[stacks 02ZI]
def IsStackInGroupoidsBySieves (p : 𝒮 ⥤ 𝒞) (J : GrothendieckTopology 𝒞) : Prop :=
  ∃ h : p.IsFiberedInGroupoids,
    haveI : p.IsFibered := h.isFibered
    (∀ (U : 𝒞) (x y : p.Fiber U), Presheaf.IsSheaf (J.over U) (p.isomPresheaf x y)) ∧
      p.HasEffectiveDescent J

/-- A stack in groupoids is fibred in groupoids. -/
theorem IsStackInGroupoidsBySieves.isFiberedInGroupoids {p : 𝒮 ⥤ 𝒞}
    {J : GrothendieckTopology 𝒞} (h : p.IsStackInGroupoidsBySieves J) :
    p.IsFiberedInGroupoids :=
  h.1

/-- A stack in groupoids is exactly a category fibred in groupoids which is a stack in the sense
of Stacks 026F; this is the equivalence (1) ⟺ (3) of Stacks 02ZJ. -/
theorem isStackInGroupoidsBySieves_iff (p : 𝒮 ⥤ 𝒞) (J : GrothendieckTopology 𝒞) :
    p.IsStackInGroupoidsBySieves J ↔ p.IsFiberedInGroupoids ∧ p.IsStack J :=
  (stackInGroupoids_tfae p J).out 1 3

/-- A stack in groupoids is a stack in the sense of Stacks 026F. -/
theorem IsStackInGroupoidsBySieves.isStack {p : 𝒮 ⥤ 𝒞} {J : GrothendieckTopology 𝒞}
    (h : p.IsStackInGroupoidsBySieves J) : p.IsStack J :=
  ((isStackInGroupoidsBySieves_iff p J).1 h).2

/-- A stack in groupoids satisfies the covering-family conditions
`CategoryTheory.Functor.IsStackInGroupoids`, at every index universe. -/
theorem IsStackInGroupoidsBySieves.isStackInGroupoids {p : 𝒮 ⥤ 𝒞}
    {J : GrothendieckTopology 𝒞} (h : p.IsStackInGroupoidsBySieves J) :
    p.IsStackInGroupoids.{w} J :=
  h.isStack.isStackInGroupoids h.isFiberedInGroupoids

end Functor

variable {𝒞 : Type u₁} {𝒳 : Type u₂} {𝒴 : Type u₃}
  [Category.{v₁} 𝒞] [Category.{v₂} 𝒳] [Category.{v₃} 𝒴]

/-- **Stacks 06P2.** Let `(𝒞, J)` be a site, let `q : 𝒴 ⥤ 𝒞` and `F ⋙ q : 𝒳 ⥤ 𝒞` be stacks in
groupoids over `𝒞`, and let `F : 𝒳 ⥤ 𝒴` be the `1`-morphism of categories over `𝒞` between
them. `𝒳` is a *gerbe over* `𝒴` if the equivalent conditions of Stacks 06P1 hold; this records
condition (2) of 06P1, `CategoryTheory.IsGerbeOver`:
(a) for `y` in `𝒴` over `U` there is a covering of `U` along whose members `y|_{U_i}` is
    isomorphic in `𝒴_{U_i}` to the image of an object of `𝒳` over `U_i`;
(b) for `x`, `x'` in `𝒳_U` and `b : F(x) ⟶ F(x')` in `𝒴_U` there is a covering of `U` along
    whose members `b|_{U_i}` is the image of a morphism `x|_{U_i} ⟶ x'|_{U_i}` of `𝒳_{U_i}`.

The two stacks-in-groupoids conditions are the standing hypotheses of the source. Condition (1)
of Stacks 06P1 is equivalent, by
`CategoryTheory.isGerbeOverStackInGroupoids_iff_isGerbe_of_factorization`. -/
@[stacks 06P2]
def IsGerbeOverStackInGroupoids (J : GrothendieckTopology 𝒞) (q : 𝒴 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒴) :
    Prop :=
  (F ⋙ q).IsStackInGroupoidsBySieves J ∧ q.IsStackInGroupoidsBySieves J ∧ IsGerbeOver J q F

/-- Unfolding `CategoryTheory.IsGerbeOverStackInGroupoids`. -/
theorem isGerbeOverStackInGroupoids_iff (J : GrothendieckTopology 𝒞) (q : 𝒴 ⥤ 𝒞)
    (F : 𝒳 ⥤ 𝒴) :
    IsGerbeOverStackInGroupoids J q F ↔
      (F ⋙ q).IsStackInGroupoidsBySieves J ∧ q.IsStackInGroupoidsBySieves J ∧
        IsGerbeOver J q F :=
  Iff.rfl

/-- A gerbe over a stack in groupoids satisfies conditions (2)(a) and (2)(b) of Stacks 06P1. -/
theorem IsGerbeOverStackInGroupoids.isGerbeOver {J : GrothendieckTopology 𝒞} {q : 𝒴 ⥤ 𝒞}
    {F : 𝒳 ⥤ 𝒴} (h : IsGerbeOverStackInGroupoids J q F) : IsGerbeOver J q F :=
  h.2.2

/-- For stacks in groupoids `F ⋙ q` and `q` over `(𝒞, J)`, with `J𝒴` the topology on `𝒴`
inherited from `(𝒞, J)`, and a factorization `F = a ⋙ F'` of `F` through an equivalence `a` over
`𝒞` with `F'` fibred in groupoids and `F' ⋙ q` a stack in groupoids, `𝒳` is a gerbe over `𝒴`
exactly when `F'` is a gerbe over the site `(𝒴, J𝒴)`: this is condition (1) of Stacks 06P1. -/
theorem isGerbeOverStackInGroupoids_iff_isGerbe_of_factorization {J : GrothendieckTopology 𝒞}
    {J𝒴 : GrothendieckTopology 𝒴} {q : 𝒴 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒴} {𝒳' : Type u₄} [Category.{v₄} 𝒳']
    {F' : 𝒳' ⥤ 𝒴} {a : 𝒳 ⥤ 𝒳'} (ha : a ⋙ F' = F)
    (e : Functor.IsEquivalenceOver (F ⋙ q) (F' ⋙ q) a)
    (hp : (F ⋙ q).IsStackInGroupoidsBySieves J) (hq : q.IsStackInGroupoidsBySieves J)
    (hp' : (F' ⋙ q).IsStackInGroupoidsBySieves J) (hF' : F'.IsFiberedInGroupoids)
    (hJ𝒴 : Functor.IsInheritedTopology.{max u₃ v₃} q J J𝒴) :
    IsGerbeOverStackInGroupoids J q F ↔ F'.IsGerbe.{max u₃ v₃} J𝒴 := by
  rw [isGerbe_of_factorization_iff_isGerbeOver ha e hp'.isStackInGroupoids
    hq.isStackInGroupoids hF' hJ𝒴]
  exact ⟨fun h => h.2.2, fun h => ⟨hp, hq, h⟩⟩

end CategoryTheory
