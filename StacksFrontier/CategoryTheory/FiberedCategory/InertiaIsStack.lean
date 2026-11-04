module

public import StacksFrontier.CategoryTheory.FiberedCategory.InertiaStackification
public import StacksFrontier.CategoryTheory.Sites.Stackification.StageThreeLocallyBijective

/-!
# The inertia of a stack is a stack

Let `(𝒞, J)` be a site and let `p : 𝒳 ⥤ 𝒞` be a stack. Its inertia `I_𝒳`
(`CategoryTheory.AbsoluteInertia`, Stacks 034I), with structure functor
`CategoryTheory.RelativeInertia.toBase p`, is again a stack. This is the absolute case of
Stacks 036Y (1).

It is read off from Stacks 06NS (`CategoryTheory.RelativeInertia.isStackification_functoriality`)
applied to the identity 1-morphism of `p`, which exhibits the stack `p` as its own
stackification: the stackification of the inertia, which 06NS shows to be a stack, is then the
inertia of `p` itself.

## Main results

* `CategoryTheory.RelativeInertia.isStack_toBase`: the inertia of a stack is a stack.
-/

@[expose] public section

namespace CategoryTheory

universe vb v u₁ u₂

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒳 : Type u₂} [Category.{v} 𝒳]

namespace RelativeInertia

/-- **The inertia of a stack is a stack** (Stacks 036Y (1), absolute case): if `p : 𝒳 ⥤ 𝒞` is a
stack over `(𝒞, J)` then so is its inertia `I_𝒳 ⥤ 𝒞`. -/
theorem isStack_toBase {p : 𝒳 ⥤ 𝒞} {J : GrothendieckTopology 𝒞} (hp : p.IsStack J) :
    (RelativeInertia.toBase p).IsStack J := by
  have := hp.isFibered
  have hG : p.IsFibredOneMorphism p (𝟭 𝒳) := Functor.IsFibredOneMorphism.id p
  refine (RelativeInertia.isStackification_functoriality hG hp (fun U x y => ⟨?_, ?_⟩)
    (fun x' => ⟨⊤, J.top_mem _, fun V f _ => ?_⟩)).1
  · exact Functor.isLocallyInjective_morPresheafMap hG
      (fun u v huv => ⟨congrArg p.map huv, ⊤, J.top_mem _, fun _ φ _ => congrArg (φ ≫ ·) huv⟩)
      U x y
  · exact Functor.isLocallySurjective_morPresheafMap hG
      (fun {a b} Gm => ⟨⊤, J.top_mem _, fun w ρ _ => ⟨ρ ≫ Gm, rfl⟩⟩) U x y
  · exact ⟨Functor.IsPreFibered.pullbackObj (rfl : p.obj x' = p.obj x') f,
      Functor.IsPreFibered.pullbackMap (rfl : p.obj x' = p.obj x') f, inferInstance⟩

end RelativeInertia

end CategoryTheory
