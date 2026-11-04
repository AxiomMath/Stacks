module

public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack
public import StacksFrontier.CategoryTheory.Sites.Stack.GroupoidOfStack
public import StacksFrontier.CategoryTheory.Sites.Stack.GroupoidTransport
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.ReverseEffective

/-!
# The cartesian groupoid of a full subcategory of a stack

Let `p : 𝒳 ⥤ 𝒞` be a fibred category over a site `(𝒞, J)` with fibre products, and let `Q` be a
property of objects of `𝒳`, closed under strongly cartesian pullback, whose full subcategory is a
stack over `𝒞`. For a smaller property `P ≤ Q` which is stable under base change and local on the
base, keep the objects satisfying `P` and only the morphisms that are strongly cartesian for `p`.
This file proves that the resulting category is a stack in groupoids over `𝒞`.

This is the shape of every moduli problem of the form "families of algebraic spaces over varying
base schemes, with cartesian squares as morphisms, satisfying a condition `P` on the structure
morphism": `p` is the projection of the comma category of all algebraic spaces over varying base
schemes, `Q` is finite typeness of the structure morphism (whose full subcategory is a stack by
Stacks 04UD), and `P` is the condition at hand.

## Main results

* `CategoryTheory.Functor.isStronglyCartesian_map_ι_of_closed`: for a property closed under
  strongly cartesian pullback, a morphism of the full subcategory that is strongly cartesian there
  is strongly cartesian in the ambient category.
* `CategoryTheory.BasedCategory.Equivalence.isStack_of_isStackInGroupoids`: being a stack in
  groupoids at the index universe `max u₁ v₁` transports along an equivalence over a base with
  fibre products to being a stack in the sense of Stacks 026F.
* `CategoryTheory.Functor.isStackInGroupoids_wideSubcategory_of_isStack_restrict`: the main
  result described above.

## Implementation notes

The proof goes through three results of the library. The full subcategory cut out by `P` inside
the stack cut out by `Q` is a stack by Stacks 04TU
(`CategoryTheory.Functor.IsStack.fullSubcategory`); its category fibred in groupoids of strongly
cartesian morphisms is a stack in groupoids by Stacks 03YI
(`CategoryTheory.Functor.IsStack.isStackInGroupoids_stronglyCartesianOver`); and that
category is equivalent over `𝒞` to the one in the statement, whose morphisms are the morphisms
strongly cartesian for the ambient `p` rather than for the restriction of `p`. The two notions of
strongly cartesian agree because both properties are closed under strongly cartesian pullback, and
the equivalence is the identity on underlying objects and morphisms. A stack in groupoids
transports along it through the two renderings of a stack compared in
`StacksFrontier/CategoryTheory/Sites/Stack/StackBridge.lean`.

The two hypotheses on `P` are stated without the chosen pullbacks of `p`: stability under base
change asks that the source of a strongly cartesian morphism into an object satisfying `P` satisfy
`P`, and locality on the base asks that an object satisfying `Q` satisfy `P` as soon as, along each
member of a covering family, it receives a strongly cartesian morphism from an object satisfying
`P`. This is how these conditions are verified for algebraic spaces, where a strongly cartesian
morphism is a cartesian square (Stacks 04U9).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

namespace Functor

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

/-- For a property `P` closed under strongly cartesian pullback for a fibred category `p`, a
morphism of the full subcategory on `P` which is strongly cartesian for the restriction of `p` is
strongly cartesian for `p`: it is cartesian for `p` by `CategoryTheory.Functor.isCartesian_map_ι`,
and cartesian morphisms of a fibred category are strongly cartesian. -/
theorem isStronglyCartesian_map_ι_of_closed (p : 𝒳 ⥤ 𝒞) (P : ObjectProperty 𝒳) [p.IsFibered]
    (h1 : ClosedUnderStronglyCartesian p P) {V U : 𝒞} {a b : P.FullSubcategory}
    (f : V ⟶ U) (φ : a ⟶ b) (h : (restrict p P).IsStronglyCartesian f φ) :
    p.IsStronglyCartesian f (P.ι.map φ) :=
  have : p.IsCartesian f (P.ι.map φ) := isCartesian_map_ι p P h1 f φ inferInstance
  inferInstance

end Functor

/-- A category over a base with fibre products which is a stack in groupoids for covering
families indexed in `Type (max u₁ v₁)` is carried by an equivalence over the base to a stack in
the sense of Stacks 026F: the reverse stack bridge
`CategoryTheory.Functor.isStack_of_isStackInGroupoids` followed by Stacks 042W. -/
theorem BasedCategory.Equivalence.isStack_of_isStackInGroupoids
    {𝒞 : Type u₁} [Category.{v₁} 𝒞] [HasPullbacks 𝒞] {𝒳 : BasedCategory.{v₂, u₂} 𝒞}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒞} (e : BasedCategory.Equivalence 𝒳 𝒴)
    {J : GrothendieckTopology 𝒞} (h : 𝒳.p.IsStackInGroupoids.{max u₁ v₁} J) :
    𝒴.p.IsStack J :=
  have : 𝒳.p.IsFibered := h.isFiberedInGroupoids.isFibered
  e.isStack J (Functor.isStack_of_isStackInGroupoids h)

/-- A stack in groupoids over a base with fibre products, at the index universe `max u₁ v₁`,
transports along an equivalence over the base to a stack in groupoids at every index universe. -/
theorem BasedCategory.Equivalence.isStackInGroupoids
    {𝒞 : Type u₁} [Category.{v₁} 𝒞] [HasPullbacks 𝒞] {𝒳 : BasedCategory.{v₂, u₂} 𝒞}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒞} (e : BasedCategory.Equivalence 𝒳 𝒴)
    {J : GrothendieckTopology 𝒞} (h : 𝒳.p.IsStackInGroupoids.{max u₁ v₁} J) :
    𝒴.p.IsStackInGroupoids.{w} J :=
  (e.isStack_of_isStackInGroupoids h).isStackInGroupoids
    (e.isFiberedInGroupoids h.isFiberedInGroupoids)

namespace Functor

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

section WideFull

variable (p : 𝒳 ⥤ 𝒞) [p.IsFibered] (Q : ObjectProperty 𝒳)
  (hQ : ClosedUnderStronglyCartesian p Q) (P : ObjectProperty 𝒳) (hPQ : P ≤ Q)

/-- The property of an object of the full subcategory on `Q` that its underlying object satisfies
`P`. -/
abbrev restrictedProperty : ObjectProperty Q.FullSubcategory := fun X => P X.obj

include hQ in
/-- Stability of `P` under base change, read in the full subcategory on `Q`. -/
theorem closedUnderStronglyCartesian_restrictedProperty
    (hP1 : ∀ {V U : 𝒞} {y x : 𝒳} (f : V ⟶ U) (φ : y ⟶ x), p.IsStronglyCartesian f φ →
      Q y → P x → P y) :
    haveI := isFibered_restrict_of_closed p Q hQ
    ClosedUnderStronglyCartesian (restrict p Q) (restrictedProperty Q P) := by
  intro V U y x f φ hφ hx
  exact isoOverId_of_prop
    (hP1 f (Q.ι.map φ) (isStronglyCartesian_map_ι_of_closed p Q hQ f φ hφ) y.property hx)

include hQ in
/-- Locality of `P` on the base, read in the full subcategory on `Q` as condition (3) of
Stacks 04TU: the chosen pullbacks along a covering family are strongly cartesian, so composing
each with the given isomorphism over the identity produces the strongly cartesian morphisms the
hypothesis asks for. -/
theorem locallyClosed_restrictedProperty (J : GrothendieckTopology 𝒞)
    (hP3 : ∀ {U : 𝒞} {ι : Type (max u₁ v₁)} (Uᵢ : ι → 𝒞) (fᵢ : (i : ι) → Uᵢ i ⟶ U),
      Sieve.generate (Presieve.ofArrows Uᵢ fᵢ) ∈ J U → ∀ x : 𝒳, p.obj x = U → Q x →
        (∀ i, ∃ (y : 𝒳) (φ : y ⟶ x), p.IsStronglyCartesian (fᵢ i) φ ∧ Q y ∧ P y) → P x) :
    haveI := isFibered_restrict_of_closed p Q hQ
    LocallyClosed (restrict p Q) (restrictedProperty Q P) J := by
  have := isFibered_restrict_of_closed p Q hQ
  intro U ι Uᵢ fᵢ hgen x hx
  refine isoOverId_of_prop (hP3 Uᵢ fᵢ hgen x.1.obj x.2 x.1.property fun i => ?_)
  obtain ⟨y', hy', e, he⟩ := hx i
  let π : (pullbackFiber (restrict p Q) x (fᵢ i)).1 ⟶ x.1 :=
    IsPreFibered.pullbackMap x.2 (fᵢ i)
  have hinv : (restrict p Q).IsHomLift (𝟙 (Uᵢ i)) e.inv := by
    have := IsHomLift.lift_id_inv (restrict p Q)
      ((restrict p Q).obj (pullbackFiber (restrict p Q) x (fᵢ i)).1) e
    rw [(pullbackFiber (restrict p Q) x (fᵢ i)).2] at this
    exact this
  have hcomp : (restrict p Q).IsStronglyCartesian (𝟙 (Uᵢ i) ≫ fᵢ i) (e.inv ≫ π) :=
    inferInstance
  rw [Category.id_comp] at hcomp
  exact ⟨y'.obj, Q.ι.map (e.inv ≫ π),
    isStronglyCartesian_map_ι_of_closed p Q hQ (fᵢ i) _ hcomp, y'.property, hy'⟩

section Comparison

variable [(stronglyCartesianOver p).IsMultiplicative]
  [(stronglyCartesianOver (restrict (restrict p Q) (restrictedProperty Q P))).IsMultiplicative]

/-- From the category of morphisms strongly cartesian for the restriction of `p` to `P` inside
`Q` to the category of morphisms of the full subcategory on `P` strongly cartesian for `p`: the
identity on underlying objects and morphisms. -/
@[simps]
def wideRestrictedToWide
    (h1 : haveI := isFibered_restrict_of_closed p Q hQ
      ClosedUnderStronglyCartesian (restrict p Q) (restrictedProperty Q P)) :
    WideSubcategory (stronglyCartesianOver (restrict (restrict p Q) (restrictedProperty Q P))) ⥤
      WideSubcategory ((stronglyCartesianOver p).inverseImage P.ι) :=
  haveI := isFibered_restrict_of_closed p Q hQ
  { obj X := ⟨⟨X.obj.obj.obj, X.obj.property⟩⟩
    map φ := ⟨ObjectProperty.homMk φ.hom.hom.hom,
      isStronglyCartesian_map_ι_of_closed p Q hQ _ _
        (isStronglyCartesian_map_ι_of_closed (restrict p Q) (restrictedProperty Q P) h1 _ _
          φ.property)⟩
    map_id _ := rfl
    map_comp _ _ := rfl }

/-- The inverse of `CategoryTheory.Functor.wideRestrictedToWide`, again the identity on
underlying objects and morphisms. -/
@[simps]
def wideToWideRestricted :
    WideSubcategory ((stronglyCartesianOver p).inverseImage P.ι) ⥤
      WideSubcategory (stronglyCartesianOver (restrict (restrict p Q) (restrictedProperty Q P)))
      where
  obj Y := ⟨⟨⟨Y.obj.obj, hPQ _ Y.obj.property⟩, Y.obj.property⟩⟩
  map ψ := ⟨ObjectProperty.homMk (ObjectProperty.homMk ψ.hom.hom),
    isStronglyCartesian_of_isStronglyCartesian_map_ι (restrict p Q) (restrictedProperty Q P) _ _
      (isStronglyCartesian_of_isStronglyCartesian_map_ι p Q _ _ ψ.property)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

end Comparison

include hQ hPQ in
/-- **The cartesian groupoid of a full subcategory of a stack is a stack in groupoids.** Let
`p : 𝒳 ⥤ 𝒞` be a fibred category over a site with fibre products, and let `Q` be a property of
objects closed under strongly cartesian pullback whose full subcategory is a stack. Let `P ≤ Q` be
stable under base change and local on the base, both read through strongly cartesian morphisms.
Then the objects satisfying `P`, with the morphisms strongly cartesian for `p`, form a stack in
groupoids, for covering families indexed in every universe.

The full subcategory on `P` inside the stack on `Q` is a stack by Stacks 04TU; its strongly
cartesian morphisms form a stack in groupoids by Stacks 03YI; and that category is the one of the
statement, up to the identification `CategoryTheory.Functor.wideRestrictedToWide`. -/
theorem isStackInGroupoids_wideSubcategory_of_isStack_restrict [HasPullbacks 𝒞]
    (J : GrothendieckTopology 𝒞) (hQs : (restrict p Q).IsStack J)
    (hP1 : ∀ {V U : 𝒞} {y x : 𝒳} (f : V ⟶ U) (φ : y ⟶ x), p.IsStronglyCartesian f φ →
      Q y → P x → P y)
    (hP3 : ∀ {U : 𝒞} {ι : Type (max u₁ v₁)} (Uᵢ : ι → 𝒞) (fᵢ : (i : ι) → Uᵢ i ⟶ U),
      Sieve.generate (Presieve.ofArrows Uᵢ fᵢ) ∈ J U → ∀ x : 𝒳, p.obj x = U → Q x →
        (∀ i, ∃ (y : 𝒳) (φ : y ⟶ x), p.IsStronglyCartesian (fᵢ i) φ ∧ Q y ∧ P y) → P x)
    [(stronglyCartesianOver p).IsMultiplicative] :
    IsStackInGroupoids.{w}
      (wideSubcategoryInclusion ((stronglyCartesianOver p).inverseImage P.ι) ⋙ P.ι ⋙ p) J := by
  have := isFibered_restrict_of_closed p Q hQ
  have h1 : ClosedUnderStronglyCartesian (restrict p Q) (restrictedProperty Q P) :=
    closedUnderStronglyCartesian_restrictedProperty p Q hQ P
    (@fun _ _ _ _ f φ => hP1 f φ)
  have hst : (restrict (restrict p Q) (restrictedProperty Q P)).IsStack J :=
    IsStack.fullSubcategory _ J hQs _ h1 (locallyClosed_restrictedProperty p Q hQ P J
      (@fun _ _ => hP3))
  have hsg := hst.isStackInGroupoids_stronglyCartesianOver.{max u₁ v₁}
  have : (restrict (restrict p Q) (restrictedProperty Q P)).IsFibered := hst.isFibered
  have := stronglyCartesianOver_isMultiplicative
    (restrict (restrict p Q) (restrictedProperty Q P))
  exact BasedCategory.Equivalence.isStackInGroupoids
    (𝒳 := BasedCategory.ofFunctor (wideSubcategoryInclusion
      (stronglyCartesianOver (restrict (restrict p Q) (restrictedProperty Q P))) ⋙
        restrict (restrict p Q) (restrictedProperty Q P)))
    (𝒴 := BasedCategory.ofFunctor
      (wideSubcategoryInclusion ((stronglyCartesianOver p).inverseImage P.ι) ⋙ P.ι ⋙ p))
    { functor := { toFunctor := wideRestrictedToWide p Q hQ P h1, w := rfl }
      inverse := { toFunctor := wideToWideRestricted p Q P hPQ, w := rfl }
      unitIso := eqToIso (BasedCategory.BasedFunctor.ext' rfl)
      counitIso := eqToIso (BasedCategory.BasedFunctor.ext' rfl) } hsg

end WideFull

end Functor

end CategoryTheory

end
