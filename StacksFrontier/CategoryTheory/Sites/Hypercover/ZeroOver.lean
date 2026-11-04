module

public import Mathlib.CategoryTheory.Sites.Hypercover.Zero
import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms of families of morphisms with fixed target

Mathlib coverage for Stacks chapter 7 (Sites and Sheaves), section 8 (Families of morphisms
with fixed target).

A family of morphisms with fixed target `{U i ⟶ S}` in a category `C` is Mathlib's
`CategoryTheory.PreZeroHypercover S`. Mathlib's `PreZeroHypercover.Hom` is a morphism
between two such families **over the same target**, i.e. a refinement; Stacks 00VT defines
the more general notion in which the targets differ and a morphism `S ⟶ T` of targets is
part of the data. This file supplies that general notion, `PreZeroHypercover.HomOver`, and
identifies it both with Mathlib's `Hom` after pushing the source family forward along the
base morphism, and — in the case of the identity base morphism — with `Hom` itself, which is
the notion of refinement of Stacks 00VT (2).

It also records that a bijective reindexing of a family leaves the *sieve* it generates
unchanged, `PreZeroHypercover.sieve₀_reindex`. Mathlib's
`CategoryTheory.PreZeroHypercover.presieve₀_reindex` says this of the generated presieve, and
the covering condition of a site is stated at the sieve.
-/

@[expose] public section

namespace CategoryTheory.PreZeroHypercover

universe w'' w' w v u

variable {C : Type u} [Category.{v} C]

/-- **A bijective reindexing of a family leaves the sieve it generates unchanged.**

Mathlib's `CategoryTheory.PreZeroHypercover.presieve₀_reindex` is this statement for the
generated *presieve*; the covering condition of a site is a condition on the generated *sieve*,
so this is the form a consumer needs. The use is to move the index type of a covering family
into a prescribed universe — along `Equiv.ulift` — without disturbing the covering property. -/
@[simp]
lemma sieve₀_reindex {S : C} (E : PreZeroHypercover.{w} S) {ι : Type w'} (e : ι ≃ E.I₀) :
    (E.reindex e).sieve₀ = E.sieve₀ := by
  simpa only [sieve₀, Sieve.ofArrows] using congrArg Sieve.generate (E.presieve₀_reindex e)

/-- **Stacks 00VT (1)**: a *morphism of families of morphisms with fixed target* from
`𝒰 = {U i ⟶ S}` to `𝒱 = {V j ⟶ T}` over a morphism `g : S ⟶ T` of the targets. It consists
of a map of index sets `s₀`, and for each index `i` a morphism `h₀ i : U i ⟶ V (s₀ i)`,
subject to commutativity of the square

```
U i          ⟶  V (s₀ i)
 |                 |
 v                 v
 S           ⟶     T
```

Mathlib's `PreZeroHypercover.Hom` is the special case in which the two families have the
same target and `g` is the identity; see `homOverIdEquivHom`. -/
@[stacks_fixed 00VT "(1) A morphism of families of morphisms with fixed target."]
structure HomOver {S T : C} (E : PreZeroHypercover.{w} S) (F : PreZeroHypercover.{w'} T)
    (g : S ⟶ T) where
  /-- The map between the indexing types of the two families. -/
  s₀ (i : E.I₀) : F.I₀
  /-- The morphism `U i ⟶ V (s₀ i)` covering `g`. -/
  h₀ (i : E.I₀) : E.X i ⟶ F.X (s₀ i)
  /-- The square over `g` commutes. -/
  w₀ (i : E.I₀) : h₀ i ≫ F.f (s₀ i) = E.f i ≫ g := by cat_disch

/-- The identity morphism of families, over the identity of the target. -/
@[simps]
def HomOver.id {S : C} (E : PreZeroHypercover.{w} S) : E.HomOver E (𝟙 S) where
  s₀ i := i
  h₀ _ := 𝟙 _
  w₀ _ := by simp

/-- Composition of morphisms of families with fixed target.

The base morphism of the composite is the *parameter* `k`, supplied with a proof `g ≫ h = k`,
rather than being `g ≫ h` itself. That is what keeps the identity case transport-free: two
refinements compose to a morphism over `𝟙 S ≫ 𝟙 S`, and `hk := Category.comp_id _` lands it over
`𝟙 S` exactly, so a lemma about `E.HomOver E (𝟙 S)` applies to it directly. Returning
`E.HomOver H (g ≫ h)` instead would force a transport in the result *type*. -/
@[simps]
def HomOver.comp {S T W : C} {E : PreZeroHypercover.{w} S} {G : PreZeroHypercover.{w'} T}
    {H : PreZeroHypercover.{w''} W} {g : S ⟶ T} {h : T ⟶ W} {k : S ⟶ W}
    (φ : E.HomOver G g) (ψ : G.HomOver H h) (hk : g ≫ h = k) : E.HomOver H k where
  s₀ i := ψ.s₀ (φ.s₀ i)
  h₀ i := φ.h₀ i ≫ ψ.h₀ (φ.s₀ i)
  w₀ i := by rw [Category.assoc, ψ.w₀, ← Category.assoc, φ.w₀, Category.assoc, hk]

variable {S T : C} (E : PreZeroHypercover.{w} S) (F : PreZeroHypercover.{w'} T)

/-- A morphism of families with fixed target over `g : S ⟶ T` is the same thing as a
refinement, in Mathlib's sense, of `F` by the family `E` pushed forward along `g` — the
family `{U i ⟶ S ⟶ T}` with the same index set. -/
@[simps]
def homOverEquivPushforwardHom (g : S ⟶ T) :
    E.HomOver F g ≃ (E.pushforward g).Hom F where
  toFun φ := { s₀ := φ.s₀, h₀ := φ.h₀, w₀ := φ.w₀ }
  invFun φ := { s₀ := φ.s₀, h₀ := φ.h₀, w₀ := φ.w₀ }

/-- **Stacks 00VT (2)**: a *refinement* is a morphism of families with fixed target whose
morphism of targets is the identity. Such morphisms are exactly Mathlib's
`PreZeroHypercover.Hom`, the morphisms of the category of families of morphisms with the
given fixed target. -/
@[stacks 00VT "(2) The special case `U = V` with `U ⟶ V` the identity: a refinement."]
def homOverIdEquivHom (E : PreZeroHypercover.{w} S) (F : PreZeroHypercover.{w'} S) :
    E.HomOver F (𝟙 S) ≃ E.Hom F where
  toFun φ := { s₀ := φ.s₀, h₀ := φ.h₀, w₀ := fun i => (φ.w₀ i).trans (Category.comp_id _) }
  invFun φ :=
    { s₀ := φ.s₀, h₀ := φ.h₀, w₀ := fun i => (φ.w₀ i).trans (Category.comp_id _).symm }

add_to_stacks 00VT "(2) Refinements of a family of morphisms with fixed target are the
  morphisms of Mathlib's category of such families; `homOverIdEquivHom` identifies them with
  the morphisms of 00VT (1) whose morphism of targets is the identity."
  CategoryTheory.PreZeroHypercover.Hom

end CategoryTheory.PreZeroHypercover
