module

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv

import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.Parity
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Data.NNRat.Floor
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Comma.Over.Basic


/-!
# The 2-Yoneda lemma (Stacks 004B)

Let `C` be a category, let `p : S ⥤ C` be fibred in groupoids and let `U` be an object
of `C`. The *evaluation functor*
`ev : Mor_{Cat/C}(C/U, S) ⥤ S_U`, `G ↦ G(id_U)`
sends a functor over `C` defined on the slice category `C/U` to its value at the
terminal object `id_U = Over.mk (𝟙 U)` of `C/U`; that value lies in the fibre of `p`
over `U` because `p ∘ G` is the structure functor `C/U ⥤ C` and `id_U` lies over `U`.
On a 2-morphism `η : G ⟶ G'`, that is a natural transformation whose components lie
over identities, evaluation returns the component at `id_U`. The 2-Yoneda lemma says
that `ev` is an equivalence of categories.

Here `ev` is `CategoryTheory.Functor.twoYonedaEvaluation` and the lemma is
`CategoryTheory.Functor.twoYonedaEvaluation_isEquivalence`, obtained by assembling
faithfulness, fullness and essential surjectivity.

Two facts drive all three halves of the proof. First, `Over.mk (𝟙 U)` is terminal in
`Over U` (`Over.mkIdTerminal`), so every object `a = (V, f)` of `C/U` admits a unique
arrow `term a : a ⟶ id_U`, and `(Over.forget U).map (term a) = f`; consequently
`G.map (term a)` lies over `f` for every functor `G` over `C`. Second, the
unique-fill-in axiom `Functor.IsFiberedInGroupoids.unique_lift` says that *every* arrow
`φ : y ⟶ x` of `S` is strongly cartesian: any `ψ : z ⟶ x` whose image factors through
`p.map φ` along a prescribed base map factors uniquely through `φ`. Comparing arrows at
`a` with arrows at `id_U` by composing with `G'.map (term a)` therefore has a unique
answer, which gives both faithfulness and fullness. Essential surjectivity uses the
other axiom, `exists_lift`, to choose a lift of `f` for each `a = (V, f)`; these chosen
lifts assemble into a functor over `C` by the same uniqueness argument.

## Stacks–Mathlib correspondence

| Stacks notion                       | Mathlib name                                  |
|-------------------------------------|-----------------------------------------------|
| `C/U`                               | `CategoryTheory.Over U`                       |
| structure functor `π_U`             | `CategoryTheory.Over.forget U`                |
| `S_U`                               | `CategoryTheory.Functor.Fiber p U`            |
| object of `Cat/C`                   | `CategoryTheory.BasedCategory C`              |
| `Mor_{Cat/C}(-,-)` objects          | `CategoryTheory.BasedFunctor` (`⥤ᵇ`)          |
| `Mor_{Cat/C}(-,-)` morphisms        | `CategoryTheory.BasedNatTrans`                |
| fibered category (003T)             | `CategoryTheory.Functor.IsFibered`            |
| strongly cartesian (02XK)           | `CategoryTheory.Functor.IsStronglyCartesian`  |
| fibered in groupoids (003V/02XL)    | `CategoryTheory.Functor.IsFiberedInGroupoids` |
| "is an equivalence"                 | `CategoryTheory.Functor.IsEquivalence`        |

The morphism category `Mor_{Cat/C}(C/U, S)` is the hom-category of `Cat/C`, i.e. the
category `BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p` of
functors over `C`, with its natural category instance (objects: based functors;
morphisms: based natural transformations).
-/

@[expose] public section

-- Load-bearing: several steps below identify `Functor.Fiber.homMk` applications whose
-- `IsHomLift` instance arguments only agree at default transparency.
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace CategoryTheory

variable {C : Type*} [Category C] {S : Type*} [Category S]

/-- Every component of a based natural transformation between based functors with source `C/U`
lies over an identity: `η.app a` lies over `𝟙 a.left`.

This is Mathlib's `BasedNatTrans.app_isHomLift` transported through `BasedCategory.ofFunctor`,
whose `p` field is only semireducibly `Over.forget U`, so that instance does not apply on the
nose. -/
instance Functor.TwoYoneda.isHomLift_app (p : S ⥤ C) (U : C)
    {G G' : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p} (η : G ⟶ G')
    (a : Over U) : p.IsHomLift (𝟙 a.left) (η.app a) := by
  have := η.isHomLift' a
  simpa [BasedCategory.ofFunctor] using this

/-- The evaluation functor `ev : Mor_{Cat/C}(C/U, S) ⥤ S_U` of the 2-Yoneda lemma.

On objects it sends a functor over `C`, `G : C/U ⥤ S` (packaged as a based functor),
to `G(id_U) = G(Over.mk (𝟙 U))`, which lies in the fibre over `U` since
`p ∘ G = π_U` and `π_U (Over.mk (𝟙 U)) = U`.

On a 2-morphism `η : G ⟶ G'` (a based natural transformation) it returns the
component `η_{(U, 𝟙 U)}`, which lies over `𝟙 U` and is therefore a morphism of `S_U`. -/
@[stacks 004B]
noncomputable def Functor.twoYonedaEvaluation (p : S ⥤ C) (U : C) :
    (BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p) ⥤ p.Fiber U where
  obj G := Functor.Fiber.mk (a := G.obj (Over.mk (𝟙 U))) (by
    have h := congrArg (·.obj (Over.mk (𝟙 U))) G.w
    simpa [BasedCategory.ofFunctor] using h)
  map {G G'} η :=
    have : p.IsHomLift (𝟙 U) (η.app (Over.mk (𝟙 U))) :=
      Functor.TwoYoneda.isHomLift_app p U η (Over.mk (𝟙 U))
    Functor.Fiber.homMk p U (η.app (Over.mk (𝟙 U)))
  map_id G := by
    apply Functor.Fiber.hom_ext
    rw [Functor.Fiber.fiberInclusion_homMk]; rfl
  map_comp {G G' G''} η μ := by
    apply Functor.Fiber.hom_ext
    rw [Functor.Fiber.fiberInclusion_homMk, Functor.map_comp,
      Functor.Fiber.fiberInclusion_homMk, Functor.Fiber.fiberInclusion_homMk]; rfl

/-- Evaluation sends a functor `G` over `C` to the object `G(id_U)` of `S`. -/
@[simp]
theorem Functor.twoYonedaEvaluation_obj (p : S ⥤ C) (U : C)
    (G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p) :
    Functor.Fiber.fiberInclusion.obj ((Functor.twoYonedaEvaluation p U).obj G) =
      G.obj (Over.mk (𝟙 U)) :=
  rfl

/-- Evaluation sends a 2-morphism `η` to its component `η_{(U, 𝟙 U)}`. -/
@[simp]
theorem Functor.twoYonedaEvaluation_map (p : S ⥤ C) (U : C)
    {G G' : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p} (η : G ⟶ G') :
    Functor.Fiber.fiberInclusion.map ((Functor.twoYonedaEvaluation p U).map η) =
      η.app (Over.mk (𝟙 U)) :=
  rfl

/-- For a based functor `G` over `C` with source `C/U` and an arrow `f` of `C/U`, the
arrow `G.map f` of `S` lies over the arrow `(Over.forget U).map f` of `C`. This is Mathlib's
`CategoryTheory.BasedFunctor.preserves_isHomLift` applied to `f`, which lies over its own image
under `Over.forget U`. -/
private lemma Functor.TwoYoneda.isHomLift_map (p : S ⥤ C) (U : C)
    (G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p)
    {a b : Over U} (f : a ⟶ b) :
    p.IsHomLift ((Over.forget U).map f) (G.map f) :=
  have : (BasedCategory.ofFunctor (Over.forget U)).p.IsHomLift ((Over.forget U).map f) f :=
    CategoryTheory.IsHomLift.map (Over.forget U) f
  CategoryTheory.BasedFunctor.preserves_isHomLift G ((Over.forget U).map f) f

/-- The unique arrow from an object `a` of `C/U` to the terminal object `Over.mk (𝟙 U)`
lies over the structure morphism `a.hom` of `a`. -/
private lemma Functor.TwoYoneda.forget_map_from_mkIdTerminal (U : C) (a : Over U) :
    (Over.forget U).map (Over.mkIdTerminal.from a) = a.hom := by
  have : Over.mkIdTerminal.from a = Over.homMk a.hom (by simp) := by
    apply Over.mkIdTerminal.hom_ext
  rw [this]; simp

/-- The image under a based functor `G` over `C` of the unique arrow `term a : a ⟶ id_U` to the
terminal object of `C/U` lies over the structure morphism `a.hom` of `a`. -/
instance Functor.TwoYoneda.isHomLift_map_from_mkIdTerminal (p : S ⥤ C) (U : C)
    (G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p) (a : Over U) :
    p.IsHomLift a.hom (G.map (Over.mkIdTerminal.from a)) := by
  have := Functor.TwoYoneda.isHomLift_map p U G (Over.mkIdTerminal.from a)
  rwa [Functor.TwoYoneda.forget_map_from_mkIdTerminal] at this

/-- When `p` is fibred in groupoids, `G.map (term a)` is *strongly cartesian* over `a.hom`.

This is the unique-fill-in axiom `IsFiberedInGroupoids.unique_lift` repackaged as
`Functor.IsStronglyCartesian` (via `IsFiberedInGroupoids.isStronglyCartesian_homLift`), so that
Mathlib's `map` / `fac` / `map_uniq` / `ext` API replaces the `eqToHom` bookkeeping that
comparing arrows at `a` with arrows at `id_U` would otherwise need. -/
lemma Functor.TwoYoneda.isStronglyCartesian_map_from_mkIdTerminal (p : S ⥤ C)
    (hp : p.IsFiberedInGroupoids) (U : C)
    (G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p) (a : Over U) :
    p.IsStronglyCartesian a.hom (G.map (Over.mkIdTerminal.from a)) :=
  hp.isStronglyCartesian_homLift a.hom _

/-- The evaluation functor of the 2-Yoneda lemma is faithful.

Let `η, η' : G ⟶ G'` be based natural transformations with `η.app id_U = η'.app id_U`.
At an object `a = (V, f)` of `C/U` both `η.app a` and `η'.app a` lie over `𝟙 V`, and
naturality along the unique arrow `term a : a ⟶ id_U` makes both composites with
`G'.map (term a)` equal to `G.map (term a) ≫ η.app id_U`. Since `G'.map (term a)` lies
over `f`, the unique-fill-in axiom of `IsFiberedInGroupoids` admits at most one arrow
over `𝟙 V` with that composite, so `η.app a = η'.app a`. -/
lemma Functor.twoYonedaEvaluation_faithful (p : S ⥤ C) (hp : p.IsFiberedInGroupoids) (U : C) :
    (Functor.twoYonedaEvaluation p U).Faithful := by
  apply Functor.Faithful.mk
  intro G G' η η' heq
  have hid : η.app (Over.mk (𝟙 U)) = η'.app (Over.mk (𝟙 U)) := congrArg Subtype.val heq
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext a
  have := Functor.TwoYoneda.isStronglyCartesian_map_from_mkIdTerminal p hp U G' a
  refine IsStronglyCartesian.ext p a.hom (G'.map (Over.mkIdTerminal.from a)) (𝟙 a.left) ?_
  rw [← η.toNatTrans.naturality, ← η'.toNatTrans.naturality, hid]

/-- The evaluation functor of the 2-Yoneda lemma is full.

Let `θ` be a morphism `G(id_U) ⟶ G'(id_U)` of the fibre `S_U`, i.e. an arrow of `S`
lying over `𝟙 U`. For each object `a = (V, f)` of `C/U` the arrow `G'.map (term a)`
lies over `f`, and `G.map (term a) ≫ θ` lies over `f = 𝟙 V ≫ f`, so the
unique-fill-in axiom of `IsFiberedInGroupoids` produces a unique
`η.app a : G.obj a ⟶ G'.obj a` lying over `𝟙 V` with
`η.app a ≫ G'.map (term a) = G.map (term a) ≫ θ`.

Uniqueness supplies the remaining data. Naturality holds because, for `g : a ⟶ a'`,
both `G.map g ≫ η.app a'` and `η.app a ≫ G'.map g` fill in the same factorization
through `G'.map (term a')` (using `g ≫ term a' = term a`, which holds since `id_U` is
terminal). Lying over an identity is exactly the based condition on `η`, and at
`a = id_U` the arrow `θ` itself is a filler, so `η.app id_U = θ` and `η` evaluates
to `θ`. -/
lemma Functor.twoYonedaEvaluation_full (p : S ⥤ C) (hp : p.IsFiberedInGroupoids) (U : C) :
    (Functor.twoYonedaEvaluation p U).Full := by
  apply Functor.Full.mk
  intro G G' θ
  have hθ : p.IsHomLift (𝟙 U) θ.1 := θ.2
  have hG : ∀ {a b : Over U} (f : a ⟶ b), p.IsHomLift ((Over.forget U).map f) (G.map f) :=
    Functor.TwoYoneda.isHomLift_map p U G
  have hG' : ∀ {a b : Over U} (f : a ⟶ b), p.IsHomLift ((Over.forget U).map f) (G'.map f) :=
    Functor.TwoYoneda.isHomLift_map p U G'
  have hsc : ∀ a : Over U, p.IsStronglyCartesian a.hom (G'.map (Over.mkIdTerminal.from a)) :=
    Functor.TwoYoneda.isStronglyCartesian_map_from_mkIdTerminal p hp U G'
  let fill : ∀ a : Over U, G.obj a ⟶ G'.obj a := fun a =>
    IsStronglyCartesian.map p a.hom (G'.map (Over.mkIdTerminal.from a))
      (Category.id_comp a.hom).symm (G.map (Over.mkIdTerminal.from a) ≫ θ.1)
  refine ⟨{
      toNatTrans := { app := fill, naturality := fun a a' g => ?_ }
      isHomLift' := fun a => ?_ }, ?_⟩
  · have hgt : g ≫ Over.mkIdTerminal.from a' = Over.mkIdTerminal.from a :=
      Over.mkIdTerminal.hom_ext _ _
    refine IsStronglyCartesian.ext p a'.hom (G'.map (Over.mkIdTerminal.from a'))
      ((Over.forget U).map g) ?_
    rw [Category.assoc, IsStronglyCartesian.fac, Category.assoc, ← G'.map_comp, hgt,
      IsStronglyCartesian.fac, ← Category.assoc, ← G.map_comp, hgt]
  · have : p.IsHomLift (𝟙 a.left) (fill a) := inferInstance
    simpa [BasedCategory.ofFunctor] using this
  · have : p.IsHomLift (𝟙 (Over.mk (𝟙 U)).left) θ.1 := hθ
    apply Functor.Fiber.hom_ext
    refine (IsStronglyCartesian.map_uniq p (Over.mk (𝟙 U)).hom
      (G'.map (Over.mkIdTerminal.from (Over.mk (𝟙 U)))) (Category.id_comp _).symm _ θ.1 ?_).symm
    rw [Over.mkIdTerminal.hom_ext (Over.mkIdTerminal.from (Over.mk (𝟙 U)))
      (𝟙 (Over.mk (𝟙 U)))]
    simp

/-!
### The essential preimage of an object of the fibre

Fix `x` in the fibre `S_U`. The declarations in `CategoryTheory.Functor.TwoYoneda`
build a functor `C/U ⥤ S` over `C` evaluating to an object isomorphic to `x`: for each
object `a = (V, f)` of `C/U` the axiom `exists_lift` provides an object `y_a` over `V`
and an arrow `φ_a : y_a ⟶ x` over `f`, which is strongly cartesian because `p` is fibred
in groupoids. The family `(y_a, φ_a)` is therefore a functor, since for `g : a ⟶ a'` there
is exactly one arrow `y_a ⟶ y_{a'}` over `g` compatible with `φ_a` and `φ_{a'}`. At the
terminal object `id_U` the arrow `φ_{id_U}` lies over `𝟙 U`, so it is an arrow of the fibre
`S_U`; since `S_U` is a groupoid, it is an isomorphism.
-/

namespace Functor.TwoYoneda

/-- Chosen lift data for an object `a` of `Over U`: an object `y` of `S` together with a
strongly cartesian arrow `φ : y ⟶ x.1` lying over the structure morphism `a.hom` of `a`. -/
structure Lift (p : S ⥤ C) (U : C) (x : p.Fiber U) (a : Over U) where
  /-- The object of `S` lying over `a.left`. -/
  y : S
  /-- The arrow of `S` from `y` to the underlying object of `x`. -/
  φ : y ⟶ x.1
  /-- The witness that `φ` is strongly cartesian over the structure morphism `a.hom` of `a`. -/
  isStronglyCartesian : p.IsStronglyCartesian a.hom φ

attribute [instance] Lift.isStronglyCartesian

/-- A choice of lift for each object of `Over U`, provided by
`Functor.IsFiberedInGroupoids.exists_lift`. It is strongly cartesian because in a category
fibred in groupoids every lift of a base morphism is
(`Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift`). -/
noncomputable def chosenLift (p : S ⥤ C) (hp : p.IsFiberedInGroupoids) (U : C) (x : p.Fiber U)
    (a : Over U) : Lift p U x a := by
  choose y φ hlift using hp.exists_lift a.hom x.1 x.2
  exact ⟨y, φ, hp.isStronglyCartesian_homLift a.hom φ⟩

variable (p : S ⥤ C) (hp : p.IsFiberedInGroupoids) (U : C) (x : p.Fiber U)

/-- The underlying functor `Over U ⥤ S` assembled from the chosen lifts of `x`.

On an arrow `g : a ⟶ a'` it is the unique arrow over `g.left` compatible with the chosen
arrows to `x`, supplied by the strong cartesianness of the chosen arrow at `a'`; the functor
laws are the corresponding uniqueness statements `IsStronglyCartesian.map_self` and
`IsStronglyCartesian.map_comp_map`. -/
@[simps]
noncomputable def liftFunctor : Over U ⥤ S where
  obj a := (chosenLift p hp U x a).y
  map {a a'} g := IsStronglyCartesian.map p a'.hom (chosenLift p hp U x a').φ (Over.w g).symm
    (chosenLift p hp U x a).φ
  map_id a := IsStronglyCartesian.map_self p a.hom (chosenLift p hp U x a).φ
  map_comp {a a' a''} g g' := (IsStronglyCartesian.map_comp_map p a''.hom
    (chosenLift p hp U x a'').φ (Over.w g').symm (Over.w g).symm (chosenLift p hp U x a').φ
    (chosenLift p hp U x a).φ).symm

/-- `liftFunctor` is a functor over `C`: composing it with `p` gives the structure
functor of `Over U`. -/
theorem liftFunctor_w : (liftFunctor p hp U x) ⋙ p = Over.forget U := by
  refine CategoryTheory.Functor.ext
    (fun a => IsHomLift.domain_eq p a.hom (chosenLift p hp U x a).φ) (fun a a' g => ?_)
  rw [Functor.comp_map, liftFunctor_map]
  simpa [Over.forget] using IsHomLift.fac' p g.left
    (IsStronglyCartesian.map p a'.hom (chosenLift p hp U x a').φ (Over.w g).symm
      (chosenLift p hp U x a).φ)

/-- The based functor `Over U ⥤ᵇ S` assembled from the chosen lifts of `x`; this is the
essential preimage of `x` under the evaluation functor. -/
noncomputable def liftBased :
    BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p where
  toFunctor := liftFunctor p hp U x
  w := liftFunctor_w p hp U x

end Functor.TwoYoneda

/-- The evaluation functor of the 2-Yoneda lemma is essentially surjective.

Given `x` in the fibre `S_U`, the based functor `Functor.TwoYoneda.liftBased` built from
the chosen lifts of `x` evaluates at the terminal object `id_U` to the chosen lift of
`𝟙 U`, and the chosen arrow `φ_{id_U}` to `x` lies over `𝟙 U`, hence is an arrow of `S_U`.
The fibre of a category fibred in groupoids is a groupoid
(`Functor.IsFiberedInGroupoids.fiber_isGroupoid`), so that arrow is an isomorphism and `x`
lies in the essential image. -/
lemma Functor.twoYonedaEvaluation_essSurj (p : S ⥤ C) (hp : p.IsFiberedInGroupoids) (U : C) :
    (Functor.twoYonedaEvaluation p U).EssSurj := by
  apply Functor.EssSurj.mk
  intro x
  have := hp.fiber_isGroupoid U
  -- `(Over.mk (𝟙 U)).hom` is `𝟙 U`, but not reducibly so; state the lift at `𝟙 U` by hand.
  have : p.IsHomLift (𝟙 U) (Functor.TwoYoneda.chosenLift p hp U x (Over.mk (𝟙 U))).φ :=
    (Functor.TwoYoneda.chosenLift p hp U x (Over.mk (𝟙 U))).isStronglyCartesian.toIsHomLift
  exact ⟨Functor.TwoYoneda.liftBased p hp U x,
    ⟨asIso (Functor.Fiber.homMk p U
      (Functor.TwoYoneda.chosenLift p hp U x (Over.mk (𝟙 U))).φ)⟩⟩

/-- **The 2-Yoneda lemma (Stacks 004B).**
Let `p : S ⥤ C` be fibred in groupoids and let `U` be an object of `C`. Then the
evaluation functor `ev : Mor_{Cat/C}(C/U, S) ⥤ S_U`, `G ↦ G(id_U)`, is an equivalence
of categories.

It is faithful, full and essentially surjective by
`Functor.twoYonedaEvaluation_faithful`, `Functor.twoYonedaEvaluation_full` and
`Functor.twoYonedaEvaluation_essSurj`, and a functor with these three properties is an
equivalence. -/
@[stacks 004B]
theorem Functor.twoYonedaEvaluation_isEquivalence (p : S ⥤ C) (hp : p.IsFiberedInGroupoids)
    (U : C) : (Functor.twoYonedaEvaluation p U).IsEquivalence := by
  have := Functor.twoYonedaEvaluation_faithful p hp U
  have := Functor.twoYonedaEvaluation_full p hp U
  have := Functor.twoYonedaEvaluation_essSurj p hp U
  exact { }

end CategoryTheory
