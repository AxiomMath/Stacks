module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalenceUniverses
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.CategoryTheory.FiberedCategory.ShrinkHomsBasedCategory
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.PullbackFiberComp

/-!
# The small model of an algebraic stack whose morphisms are not small

An algebraic stack over a scheme `S` of a big fppf site may come with a total category whose
morphisms live in a universe above that of the schemes: a stackification, such as a quotient stack
or the inverse image of a stack along an enlargement of the big site, is of that kind. The
2-category of algebraic stacks of Stacks 03YP is formed at the universes of the site, so such an
algebraic stack is an object of it only after its hom types have been brought down.

They can be: the diagonal of an algebraic stack is representable by algebraic spaces, so the
morphisms between two objects of one fibre are the sections of an algebraic space over the
scheme the fibre lies over, and these form a set in the universe of the schemes; a morphism
between arbitrary objects is a morphism of the site together with a morphism of a fibre. So the
total category is locally small at the universe of the schemes, and
`CategoryTheory.BasedCategory.shrinkHoms` produces a small model of it.

## Main results

* `AlgebraicGeometry.Stack.small_fiber_hom_of_isAlgebraicSpaceIsomPresheaf`: the morphisms
  between two objects of a fibre form a small type when the `Isom` sheaves are algebraic spaces.
* `AlgebraicGeometry.Stack.locallySmall_of_isAlgebraicSpaceIsomPresheaf` and
  `AlgebraicGeometry.Stack.locallySmall_of_isAlgebraicStack`: the total category is locally small.
* `AlgebraicGeometry.Stack.isAlgebraicStack_shrinkHoms`: the small model is an algebraic stack.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.smallModel`: the small model of an algebraic stack,
  as an object of the 2-category of algebraic stacks of Stacks 03YP, together with
  `AlgebraicGeometry.Stack.AlgebraicStacks.smallModelEquivalenceOver`, its equivalence over the
  site with the algebraic stack it models.

## Implementation notes

The fibre morphisms are read at the identity of the base object of the fibre: there the
presheaf `Isom(x, y)` of Stacks 02ZB has the morphisms `x ⟶ y` as sections, via the chosen
pullback along the identity, and its value at the object of the iterated slice corresponding to
that identity is, through the comparison isomorphism `IsAlgebraicSpaceIsomPresheaf` provides,
in bijection with the value of an algebraic space, which is a type in the universe of the
schemes.

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 02ZB](https://stacks.math.columbia.edu/tag/02ZB)
* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u w v t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The morphisms between two objects of a fibre form a small type** when the `Isom` sheaves of
the category fibred in groupoids are algebraic spaces (condition (2) of Stacks 045G). -/
theorem small_fiber_hom_of_isAlgebraicSpaceIsomPresheaf
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, t} (BigFppfOver B S hS))
    (h : IsAlgebraicSpaceIsomPresheaf B S hS 𝒳) {U : BigFppfOver B S hS}
    (x y : 𝒳.val.p.Fiber U) : Small.{u} (x ⟶ y) := by
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  obtain ⟨F, -, ⟨e⟩⟩ := h U x y
  let o : Over U.left := (Over.iteratedSliceForward U).obj (Over.mk (𝟙 U))
  -- the value of `Isom(x, y)` at `o` is small, being in bijection with a value of `F`
  have h₁ : Small.{u} ((𝒳.val.p.isomPresheaf x y).obj
      (op ((Over.iteratedSliceBackward U).obj o))) :=
    ⟨⟨F.obj (op o), ⟨Equiv.ulift.symm.trans ((e.app (op o)).toEquiv.symm.trans Equiv.ulift)⟩⟩⟩
  -- the object of `Over U` it lies over is the identity of `U`, up to isomorphism
  let i : Over.mk (𝟙 U) ≅ (Over.iteratedSliceBackward U).obj o :=
    (Over.iteratedSliceEquiv U).unitIso.app (Over.mk (𝟙 U))
  have h₂ : Small.{u} ((𝒳.val.p.isomPresheaf x y).obj (op (Over.mk (𝟙 U)))) :=
    small_map ((𝒳.val.p.isomPresheaf x y).mapIso i.op).toEquiv.symm
  -- there `Isom(x, y)` is `Mor(x, y)`, whose sections are the morphisms of the fibre
  have h₃ : Small.{u} ((𝒳.val.p.morPresheaf x y).obj (op (Over.mk (𝟙 U)))) :=
    small_map ((isomPresheafIsoMorPresheaf 𝒳.val.p 𝒳.isFiberedInGroupoids x y).app
      (op (Over.mk (𝟙 U)))).toEquiv.symm
  have : Small.{u} (𝒳.val.p.pullbackFiber x (𝟙 U) ⟶ 𝒳.val.p.pullbackFiber y (𝟙 U)) := h₃
  exact small_map (Iso.homCongr (Functor.pullbackFiberIdIso x).symm
    (Functor.pullbackFiberIdIso y).symm)

/-- **The total category is locally small** when the `Isom` sheaves are algebraic spaces: a
morphism `a ⟶ b` is its image `g` in the site together with the vertical morphism through which it
factors over the chosen cartesian lift of `g` at `b`, and both range over small types. -/
theorem locallySmall_of_isAlgebraicSpaceIsomPresheaf
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, t} (BigFppfOver B S hS))
    (h : IsAlgebraicSpaceIsomPresheaf B S hS 𝒳) : LocallySmall.{u} 𝒳.val.obj := by
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  refine ⟨fun a b => ?_⟩
  set p := 𝒳.val.p
  have hsub (g : p.obj a ⟶ p.obj b) : Small.{u} {φ : a ⟶ b // p.map φ = g} := by
    let χ := Functor.IsPreFibered.pullbackMap (p := p) (rfl : p.obj b = p.obj b) g
    let x : p.Fiber (p.obj a) := Functor.Fiber.mk (rfl : p.obj a = p.obj a)
    let y : p.Fiber (p.obj a) :=
      Functor.Fiber.mk (Functor.IsPreFibered.pullbackObj_proj (p := p) rfl g)
    have := small_fiber_hom_of_isAlgebraicSpaceIsomPresheaf B S hS 𝒳 h x y
    have hlift : ∀ φ : {φ : a ⟶ b // p.map φ = g}, p.IsHomLift g φ.1 := fun φ => by
      obtain ⟨φ, rfl⟩ := φ
      infer_instance
    let fac : {φ : a ⟶ b // p.map φ = g} → (x ⟶ y) := fun φ =>
      have := hlift φ
      Functor.Fiber.homMk p (p.obj a) (Functor.IsCartesian.map p g χ φ.1)
    refine small_of_injective (f := fac) fun φ₁ φ₂ hφ => ?_
    have := hlift φ₁
    have := hlift φ₂
    have h' : Functor.IsCartesian.map p g χ φ₁.1 = Functor.IsCartesian.map p g χ φ₂.1 :=
      congrArg Subtype.val hφ
    apply Subtype.ext
    rw [← Functor.IsCartesian.fac p g χ φ₁.1, ← Functor.IsCartesian.fac p g χ φ₂.1, h']
  exact small_of_injective
    (f := fun φ : a ⟶ b => (⟨p.map φ, φ, rfl⟩ : Σ g : p.obj a ⟶ p.obj b,
      {φ : a ⟶ b // p.map φ = g}))
    (fun φ ψ hφψ => congrArg (fun s : Σ g : p.obj a ⟶ p.obj b,
      {φ : a ⟶ b // p.map φ = g} => s.2.1) hφψ)

/-- **The total category of an algebraic stack is locally small** at the universe of the schemes,
whatever the universe of its morphisms: its diagonal is representable by algebraic spaces. -/
theorem locallySmall_of_isAlgebraicStack {𝒳 : BasedCategory.{v, u + 1} (BigFppfOver B S hS)}
    (h : IsAlgebraicStack.{u, w} B S hS 𝒳) : LocallySmall.{u} 𝒳.obj :=
  locallySmall_of_isAlgebraicSpaceIsomPresheaf B S hS (CatFiberedInGroupoids.mk 𝒳 h.1)
    ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS
      (CatFiberedInGroupoids.mk 𝒳 h.1)).mp h.2.2.1)

/-- **The small model of an algebraic stack is an algebraic stack**, by Stacks 03YQ in independent
universes. -/
theorem isAlgebraicStack_shrinkHoms {𝒳 : BasedCategory.{v, u + 1} (BigFppfOver B S hS)}
    (h : IsAlgebraicStack.{u, w} B S hS 𝒳) :
    letI := locallySmall_of_isAlgebraicStack B S hS h
    IsAlgebraicStack.{u, w} B S hS (𝒳.shrinkHoms.{u}) :=
  let := locallySmall_of_isAlgebraicStack B S hS h
  isAlgebraicStack_of_equivalenceOver B S hS (BasedCategory.shrinkHomsEquivalenceOver 𝒳) h

/-- **The small model of an algebraic stack**, as an object of the 2-category of algebraic stacks
of Stacks 03YP: its total category is that of the given algebraic stack with the hom types
brought down to the universe of the schemes. -/
noncomputable def AlgebraicStacks.smallModel
    (𝒳 : BasedCategory.{v, u + 1} (BigFppfOver B S hS))
    (h : IsAlgebraicStack.{u, w} B S hS 𝒳) : AlgebraicStacks.{u, w} B S hS :=
  letI := locallySmall_of_isAlgebraicStack B S hS h
  ⟨CatFiberedInGroupoids.mk (𝒳.shrinkHoms.{u}) (isAlgebraicStack_shrinkHoms B S hS h).1,
    isAlgebraicStack_shrinkHoms B S hS h⟩

/-- **An algebraic stack is equivalent over the site to its small model.** -/
noncomputable def AlgebraicStacks.smallModelEquivalenceOver
    (𝒳 : BasedCategory.{v, u + 1} (BigFppfOver B S hS))
    (h : IsAlgebraicStack.{u, w} B S hS 𝒳) :
    StacksRepresentableCFG.EquivalenceOver 𝒳.p (smallModel B S hS 𝒳 h).val.val.p :=
  letI := locallySmall_of_isAlgebraicStack B S hS h
  BasedCategory.shrinkHomsEquivalenceOver 𝒳

end AlgebraicGeometry.Stack

end
