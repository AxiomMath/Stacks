module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleHigherBaseChangePasting
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SystemPullbackComparison

/-!
# The action of `R^q g_*` on morphisms over an étale square

Let
```
Y --e--> X
|h       |g
v        v
S' --a--> S
```
be a commutative square of schemes whose base change map `a⁻¹ R^q g_* ⟶ R^q h_* e⁻¹`
(`Stacks.EtaleCohomology.higherBaseChangeMapAb`) is invertible, e.g. a cartesian square with `a`
étale. A morphism `α : e⁻¹ A ⟶ e⁻¹ K` of abelian sheaves on `Y` then acts on the inverse images
along `a` of the higher direct images: `R^q h_* α`, read through the two base change
isomorphisms, is a morphism `a⁻¹ R^q g_* A ⟶ a⁻¹ R^q g_* K`
(`Stacks.EtaleCohomology.higherDirectImageLocalMap`). This is how `R^q g_*` acts on morphisms
that are only defined étale locally on the base: for `a` the structure morphism of an étale
`S`-scheme and `e` its base change, `α` is a morphism between the restrictions of `A` and `K`.

The action is functorial and additive, it is `a⁻¹ R^q g_*` on morphisms coming from `X`
(`Stacks.EtaleCohomology.higherDirectImageLocalMap_map`), and it is compatible with a further
pullback along `b : S'' ⟶ S'`: pulling the action back along `b` is the action of the pasted
square on the pullback of `α` (`Stacks.EtaleCohomology.higherDirectImageLocalMap_paste`), by
the pasting law of the base change maps
(`Stacks.EtaleCohomology.higherBaseChangeMapAb_paste_app`).

## Main definitions

* `Stacks.EtaleCohomology.higherDirectImageLocalMap`.

## Main results

* `Stacks.EtaleCohomology.higherDirectImageLocalMap_eq_iff`.
* `Stacks.EtaleCohomology.higherDirectImageLocalMap_comp`.
* `Stacks.EtaleCohomology.higherDirectImageLocalMap_map`.
* `Stacks.EtaleCohomology.higherDirectImageLocalMap_paste`.
* `Stacks.EtaleCohomology.higherDirectImageLocalMap_paste'`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

section LocalAction

variable {X S S' Y : Scheme.{u}} (g : X ⟶ S) (a : S' ⟶ S) (h : Y ⟶ S') (e : Y ⟶ X)
  (w : h ≫ a = e ≫ g) (q : ℕ)

/-- **The base change map of a square is invertible in degree `q`**, at every abelian sheaf. -/
def HigherBaseChangeIsIso : Prop :=
  ∀ F : Sheaf (smallEtaleTopology X) Ab.{u + 1},
    IsIso ((higherBaseChangeMapAb a g h e w q).app F)

variable {g a h e w q}

/-- **The action of `R^q g_*` on a morphism over an étale square**: for
`α : e⁻¹ A ⟶ e⁻¹ K`, the morphism `R^q h_* α`, read through the base change isomorphisms
`a⁻¹ R^q g_* ≅ R^q h_* e⁻¹` at `A` and at `K`. -/
def higherDirectImageLocalMap (hθ : HigherBaseChangeIsIso g a h e w q)
    {A K : Sheaf (smallEtaleTopology X) Ab.{u + 1}}
    (α : (smallEtalePullbackAb e).obj A ⟶ (smallEtalePullbackAb e).obj K) :
    (smallEtalePullbackAb a).obj (((smallEtalePushforwardAb g).rightDerived q).obj A) ⟶
      (smallEtalePullbackAb a).obj (((smallEtalePushforwardAb g).rightDerived q).obj K) :=
  (higherBaseChangeMapAb a g h e w q).app A ≫
    ((smallEtalePushforwardAb h).rightDerived q).map α ≫
      @inv _ _ _ _ ((higherBaseChangeMapAb a g h e w q).app K) (hθ K)

/-- **The action is characterized by the base change maps**: `ψ` is the action of `α` if and
only if it intertwines `R^q h_* α` with the base change maps. -/
theorem higherDirectImageLocalMap_eq_iff (hθ : HigherBaseChangeIsIso g a h e w q)
    {A K : Sheaf (smallEtaleTopology X) Ab.{u + 1}}
    (α : (smallEtalePullbackAb e).obj A ⟶ (smallEtalePullbackAb e).obj K)
    (ψ : (smallEtalePullbackAb a).obj (((smallEtalePushforwardAb g).rightDerived q).obj A) ⟶
      (smallEtalePullbackAb a).obj (((smallEtalePushforwardAb g).rightDerived q).obj K)) :
    higherDirectImageLocalMap hθ α = ψ ↔
      (higherBaseChangeMapAb a g h e w q).app A ≫
          ((smallEtalePushforwardAb h).rightDerived q).map α =
        ψ ≫ (higherBaseChangeMapAb a g h e w q).app K := by
  have := hθ K
  rw [higherDirectImageLocalMap, ← Category.assoc, IsIso.comp_inv_eq]

/-- The action of `α`, followed by the base change map at `K`, is the base change map at `A`
followed by `R^q h_* α`. -/
theorem higherDirectImageLocalMap_comp_higherBaseChangeMapAb
    (hθ : HigherBaseChangeIsIso g a h e w q) {A K : Sheaf (smallEtaleTopology X) Ab.{u + 1}}
    (α : (smallEtalePullbackAb e).obj A ⟶ (smallEtalePullbackAb e).obj K) :
    higherDirectImageLocalMap hθ α ≫ (higherBaseChangeMapAb a g h e w q).app K =
      (higherBaseChangeMapAb a g h e w q).app A ≫
        ((smallEtalePushforwardAb h).rightDerived q).map α :=
  ((higherDirectImageLocalMap_eq_iff hθ α _).1 rfl).symm

/-- The action of the identity is the identity. -/
@[simp]
theorem higherDirectImageLocalMap_id (hθ : HigherBaseChangeIsIso g a h e w q)
    (A : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    higherDirectImageLocalMap hθ (𝟙 ((smallEtalePullbackAb e).obj A)) = 𝟙 _ := by
  rw [higherDirectImageLocalMap_eq_iff, CategoryTheory.Functor.map_id]
  simp

/-- **The action is functorial.** -/
theorem higherDirectImageLocalMap_comp (hθ : HigherBaseChangeIsIso g a h e w q)
    {A K L : Sheaf (smallEtaleTopology X) Ab.{u + 1}}
    (α : (smallEtalePullbackAb e).obj A ⟶ (smallEtalePullbackAb e).obj K)
    (β : (smallEtalePullbackAb e).obj K ⟶ (smallEtalePullbackAb e).obj L) :
    higherDirectImageLocalMap hθ (α ≫ β) =
      higherDirectImageLocalMap hθ α ≫ higherDirectImageLocalMap hθ β := by
  rw [higherDirectImageLocalMap_eq_iff, CategoryTheory.Functor.map_comp, Category.assoc,
    higherDirectImageLocalMap_comp_higherBaseChangeMapAb,
    ← Category.assoc, ← Category.assoc,
    higherDirectImageLocalMap_comp_higherBaseChangeMapAb, Category.assoc]

/-- **The action is additive.** -/
theorem higherDirectImageLocalMap_add (hθ : HigherBaseChangeIsIso g a h e w q)
    {A K : Sheaf (smallEtaleTopology X) Ab.{u + 1}}
    (α β : (smallEtalePullbackAb e).obj A ⟶ (smallEtalePullbackAb e).obj K) :
    higherDirectImageLocalMap hθ (α + β) =
      higherDirectImageLocalMap hθ α + higherDirectImageLocalMap hθ β := by
  rw [higherDirectImageLocalMap_eq_iff, CategoryTheory.Functor.map_add, Preadditive.comp_add,
    Preadditive.add_comp, higherDirectImageLocalMap_comp_higherBaseChangeMapAb,
    higherDirectImageLocalMap_comp_higherBaseChangeMapAb]

/-- **On a morphism coming from `X`, the action is `a⁻¹ R^q g_*` of it**: the base change map is
natural. -/
theorem higherDirectImageLocalMap_map (hθ : HigherBaseChangeIsIso g a h e w q)
    {A K : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (u' : A ⟶ K) :
    higherDirectImageLocalMap hθ ((smallEtalePullbackAb e).map u') =
      (smallEtalePullbackAb a).map (((smallEtalePushforwardAb g).rightDerived q).map u') := by
  rw [higherDirectImageLocalMap_eq_iff]
  exact ((higherBaseChangeMapAb a g h e w q).naturality u').symm

/-- **The action is compatible with a further pullback.** For a second square
`h' ≫ b = e' ≫ h` under the first one, the pullback along `b` of the action of `α`, read
through the composition isomorphisms of inverse images, is the action of the outer rectangle on
the pullback of `α` along `e'`. -/
theorem higherDirectImageLocalMap_paste (hθ : HigherBaseChangeIsIso g a h e w q)
    {S'' Y' : Scheme.{u}} (b : S'' ⟶ S') (h' : Y' ⟶ S'') (e' : Y' ⟶ Y) (w' : h' ≫ b = e' ≫ h)
    (hθP : HigherBaseChangeIsIso g (b ≫ a) h' (e' ≫ e)
      (smallEtaleRectangle_comm g h h' a b e e' w w') q)
    {A K : Sheaf (smallEtaleTopology X) Ab.{u + 1}}
    (α : (smallEtalePullbackAb e).obj A ⟶ (smallEtalePullbackAb e).obj K) :
    higherDirectImageLocalMap hθP ((smallEtalePullbackAbCompIso e' e).inv.app A ≫
        (smallEtalePullbackAb e').map α ≫ (smallEtalePullbackAbCompIso e' e).hom.app K) =
      (smallEtalePullbackAbCompIso b a).inv.app _ ≫
        (smallEtalePullbackAb b).map (higherDirectImageLocalMap hθ α) ≫
          (smallEtalePullbackAbCompIso b a).hom.app _ := by
  rw [higherDirectImageLocalMap_eq_iff, higherBaseChangeMapAb_paste_app g h h' a b e e' w w' q A,
    higherBaseChangeMapAb_paste_app g h h' a b e e' w w' q K]
  have hnat := (higherBaseChangeMapAb b h h' e' w' q).naturality α
  have hspec := higherDirectImageLocalMap_comp_higherBaseChangeMapAb hθ α
  simp only [Functor.comp_map] at hnat
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app_assoc,
    Iso.hom_inv_id_app_assoc]
  rw [CategoryTheory.Functor.map_comp ((smallEtalePushforwardAb h').rightDerived q),
    reassoc_of% hnat.symm, ← CategoryTheory.Functor.map_comp_assoc (smallEtalePullbackAb b),
    ← hspec, CategoryTheory.Functor.map_comp_assoc]

/-- **The compatibility with a further pullback, with the composites named**: as
`Stacks.EtaleCohomology.higherDirectImageLocalMap_paste`, for an outer square whose legs `a''`,
`e''` are equal (not necessarily syntactically) to the composites `b ≫ a`, `e' ≫ e`. -/
theorem higherDirectImageLocalMap_paste' (hθ : HigherBaseChangeIsIso g a h e w q)
    {S'' Y' : Scheme.{u}} (b : S'' ⟶ S') (h' : Y' ⟶ S'') (e' : Y' ⟶ Y) (w' : h' ≫ b = e' ≫ h)
    (a'' : S'' ⟶ S) (ha : a'' = b ≫ a) (e'' : Y' ⟶ X) (he : e'' = e' ≫ e)
    (w'' : h' ≫ a'' = e'' ≫ g) (hθP : HigherBaseChangeIsIso g a'' h' e'' w'' q)
    {A K : Sheaf (smallEtaleTopology X) Ab.{u + 1}}
    (α : (smallEtalePullbackAb e).obj A ⟶ (smallEtalePullbackAb e).obj K) :
    higherDirectImageLocalMap hθP ((smallEtalePullbackAbCompIso' e' e e'' he).inv.app A ≫
        (smallEtalePullbackAb e').map α ≫ (smallEtalePullbackAbCompIso' e' e e'' he).hom.app K) =
      (smallEtalePullbackAbCompIso' b a a'' ha).inv.app _ ≫
        (smallEtalePullbackAb b).map (higherDirectImageLocalMap hθ α) ≫
          (smallEtalePullbackAbCompIso' b a a'' ha).hom.app _ := by
  subst ha he
  have hrfl : ∀ {X₁ X₂ X₃ : Scheme.{u}} (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃),
      smallEtalePullbackAbCompIso' f₁ f₂ (f₁ ≫ f₂) rfl = smallEtalePullbackAbCompIso f₁ f₂ :=
    fun f₁ f₂ => (smallEtalePullbackAbCompIso'_rfl f₁ f₂).trans
      (smallEtalePullbackAbCompIso_eq_leftAdjointCompIso f₁ f₂).symm
  rw [hrfl, hrfl]
  exact higherDirectImageLocalMap_paste hθ b h' e' w' hθP α

end LocalAction

end Stacks.EtaleCohomology

end
