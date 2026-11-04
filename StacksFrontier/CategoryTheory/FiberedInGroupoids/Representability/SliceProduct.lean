module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Slice

/-!
# The 2-fibre product over a slice is fibred in groupoids (Stacks 02Y6)

Fix a base category `𝒞` and an object `U` of `𝒞`. Let `𝒳`, `𝒴` be categories fibred in groupoids
over `𝒞`, let `F : 𝒳 ⥤ 𝒴` be a 1-morphism over `𝒞` and let `G : 𝒞/U ⥤ 𝒴` be a 1-morphism over
`𝒞`. Stacks 02Y6 (Lemma 4.42.2) says that the first projection

`(𝒞/U) ×_𝒴 𝒳 ⟶ 𝒞/U`

is a category fibred in groupoids — over the slice `𝒞/U`, not merely over `𝒞`.

The proof is the one in the Stacks Project: Stacks 0041
(`CategoryTheory.TwoFibreProductOver.isFiberedInGroupoids`) gives that the structure functor of
the 2-fibre product to `𝒞` is fibred in groupoids, and that structure functor factors through the
slice as `π₁ ⋙ Over.forget U` (`CategoryTheory.TwoFibreProductOver.fst_comp_eq`), so Stacks 02XT
(`CategoryTheory.Functor.IsFiberedInGroupoids.of_comp_over`) descends the conclusion to `𝒞/U`.

Applying Stacks 0041 needs the slice itself to be fibred in groupoids over `𝒞`, which is the
standard fact recorded here as `over_forget`.

## Main results

* `CategoryTheory.Functor.IsFiberedInGroupoids.over_forget`: the slice `𝒞/U` is fibred in
  groupoids over `𝒞`.
* `CategoryTheory.Functor.IsFiberedInGroupoids.over_map`: the functor `Over.map g` between
  slices induced by a morphism `g` of `𝒞` is fibred in groupoids.
* `CategoryTheory.TwoFibreProductOver.fst_isFiberedInGroupoids`: **Stacks 02Y6**.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]
variable {𝒳 : Type u₂} [Category.{v₂} 𝒳]
variable {𝒴 : Type u₃} [Category.{v₃} 𝒴]

/-- The slice category `𝒞/U` is fibred in groupoids over `𝒞` via `Over.forget U`.

A morphism `f : V ⟶ x.left` of `𝒞` lifts to the object `Over.mk (f ≫ x.hom)` and the morphism
`Over.homMk f`; and a fill-in in `𝒞` is automatically a morphism of `𝒞/U`, uniquely so because
`Over.forget U` is faithful. -/
theorem Functor.IsFiberedInGroupoids.over_forget (U : 𝒞) :
    (Over.forget U).IsFiberedInGroupoids := by
  constructor
  · intro V W f x hx
    exact ⟨Over.mk (f ≫ eqToHom hx.symm ≫ x.hom), Over.homMk (f ≫ eqToHom hx.symm) (by simp),
      IsHomLift.of_fac' (Over.forget U) f _ rfl hx (by simp)⟩
  · intro x y z φ ψ h hcomp
    simp only [Over.forget_map] at hcomp
    have hw : h ≫ y.hom = z.hom := by
      rw [← Over.w φ, ← Category.assoc, hcomp, Over.w ψ]
    exact ⟨Over.homMk h hw, ⟨rfl, Over.OverMorphism.ext (by simpa using hcomp)⟩,
      fun _ ⟨h₁, _⟩ ↦ Over.OverMorphism.ext (by simpa using h₁)⟩

/-- The functor `Over.map g : 𝒞/U ⥤ 𝒞/S` induced by a morphism `g : U ⟶ S` of `𝒞` is fibred in
groupoids.

Composing it with `Over.forget S` gives `Over.forget U`, which is fibred in groupoids by
`over_forget`, so `of_comp_over` descends the conclusion to `𝒞/S`. -/
theorem Functor.IsFiberedInGroupoids.over_map {U S : 𝒞} (g : U ⟶ S) :
    (Over.map g).IsFiberedInGroupoids :=
  Functor.IsFiberedInGroupoids.of_comp_over S (Over.forget U) (Over.map g)
    (Over.mapForget_eq g) (Functor.IsFiberedInGroupoids.over_forget U)

/-- **Stacks 02Y6.** Let `𝒳`, `𝒴` be categories fibred in groupoids over `𝒞`, let `F : 𝒳 ⥤ 𝒴` and
`G : 𝒞/U ⥤ 𝒴` be 1-morphisms over `𝒞`. Then the first projection of the 2-fibre product
`(𝒞/U) ×_𝒴 𝒳 ⟶ 𝒞/U` is a category fibred in groupoids over the slice `𝒞/U`. -/
@[stacks 02Y6]
theorem TwoFibreProductOver.fst_isFiberedInGroupoids (U : 𝒞) (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞)
    (F : 𝒳 ⥤ 𝒴) (G : Over U ⥤ 𝒴)
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (hF : F ⋙ p𝒴 = p𝒳) (hG : G ⋙ p𝒴 = Over.forget U) :
    (TwoFibreProductOver.fst (Over.forget U) p𝒳 p𝒴 G F).IsFiberedInGroupoids :=
  Functor.IsFiberedInGroupoids.of_comp_over U _ _ fst_comp_eq
    (isFiberedInGroupoids _ _ _ _ _ (Functor.IsFiberedInGroupoids.over_forget U) h𝒳 h𝒴 hG hF)

end CategoryTheory
