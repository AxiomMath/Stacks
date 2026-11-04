module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EffectiveDescentData

/-!
# Descent data for schemes relative to a single morphism

Let `f : X ⟶ S` be a morphism of schemes and let `V` be a scheme over `X`. A descent datum
for `V/X/S` is an isomorphism `φ : V ×_S X ≅ X ×_S V` of schemes over `X ×_S X` satisfying the
cocycle condition on `X ×_S X ×_S X`, and a morphism of descent data is a morphism of
`X`-schemes commuting with the two gluing isomorphisms. This file names that category and
gives it the interface of a single morphism, rather than of the one-member family it is
realized as.

## Main definitions

* `AlgebraicGeometry.DescentDatum` is the category of descent data relative to one morphism
  of schemes, and `AlgebraicGeometry.DescentDatum.Hom` is a morphism of such data.
* `AlgebraicGeometry.DescentDatum.mk'` builds a descent datum out of exactly the three pieces
  of data the definition asks for; `AlgebraicGeometry.DescentDatum.mk'_over` and
  `AlgebraicGeometry.DescentDatum.mk'_transition` read those pieces back off.
* `AlgebraicGeometry.DescentDatum.over` is the scheme `V` over `X`,
  `AlgebraicGeometry.DescentDatum.transition` is the gluing isomorphism `φ`, and
  `AlgebraicGeometry.DescentDatum.transitionPullbackIso` is `φ` on the literal fibre products
  `V ×_S X` and `X ×_S V`.
* `AlgebraicGeometry.DescentDatum.forget` sends a descent datum to its underlying `X`-scheme.
* `AlgebraicGeometry.DescentDatum.canonical` sends a scheme over `S` to its canonical descent
  datum relative to `f`.
* `AlgebraicGeometry.DescentDatum.diagLeft` and `AlgebraicGeometry.DescentDatum.diagRight`
  are the two base changes of `V` along the diagonal `Δ : X ⟶ X ×_S X`, viewed inside
  `V ×_S X` and inside `X ×_S V`, and `AlgebraicGeometry.DescentDatum.diagonalTransition` is
  `Δ^*φ : V ⟶ V`.

## Main results

* `AlgebraicGeometry.DescentDatum.diagonalTransition_eq_id`: **`Δ^*φ` is the identity.** This
  is the identity the source leaves as an exercise. Equivalently
  `AlgebraicGeometry.DescentDatum.diagLeft_comp_transition_hom` says that `φ` carries the
  diagonal copy of `V` inside `V ×_S X` to the diagonal copy inside `X ×_S V`.
* `AlgebraicGeometry.DescentDatum.diagHom_idem` is the half of that identity which comes from
  the cocycle condition, and `AlgebraicGeometry.DescentDatum.diagHom_comp_inv` the half which
  comes from `φ` being invertible.
* `AlgebraicGeometry.DescentDatum.isEffective_canonical`: the canonical descent datum of a
  scheme over `S` is effective. In particular the category is never empty and effectivity is
  never vacuous.

## Implementation notes

**The substrate.** A descent datum relative to `f : X ⟶ S` is here *defined* to be an
`AlgebraicGeometry.DescentData` for the one-member family `fun _ : Unit ↦ f`, which is the
representation `StacksFrontier.AlgebraicGeometry.Descent.Scheme.FamilyCoproduct` and
`StacksFrontier.AlgebraicGeometry.Descent.Germs.EffectiveDescentData` already use. Three things
come with that choice and would have to be bridged by hand after any other:
the category structure, the canonical-datum functor and effectivity;
`AlgebraicGeometry.DescentData.familyCoproductEquivalence`, which compares descent data for a
family with descent data for the single morphism out of its disjoint union, so that
comparison now reads as a statement about this category; and the pullback functor of a
morphism of families. The alternative substrate, Mathlib's
`CategoryTheory.Pseudofunctor.DescentData`, would need the base-change pseudofunctor on
schemes, which the repository does not have, and presents the gluing data as a morphism over
every object mapping to both members rather than as one isomorphism over `X ×_S X`, so it is
not this definition's shape either.

**What is added on top.** The accessors take no index: `over`, `transition` and
`cocycle_triangle` are the three components of the definition, `mk'` is the constructor in
the same terms, and `transitionPullbackIso` is the gluing isomorphism transported to the
literal fibre products, which is the form in which consumers meet it. Everything inherited
from the family case — the category instance, extensionality, the pullback functors — applies
unchanged, so it is not restated.

**The diagonal identity.** `diagHom` is `Δ^*φ` computed in `Over S`, where the products
live; `diagonalTransition` is the same morphism recorded as a map of `X`-schemes, which it is
because `φ` lies over `X ×_S X`. The proof that it is the identity is in two independent
halves. Composing the cocycle condition with the diagonal of `V` in the triple product shows
`Δ^*φ` is idempotent; composing `φ` with its inverse shows `Δ^*φ` has a right inverse; and an
idempotent with a right inverse is the identity.

## References

* [Stacks Project, Tag 023V](https://stacks.math.columbia.edu/tag/023V)
* [Stacks Project, Tag 023W](https://stacks.math.columbia.edu/tag/023W)
* [Stacks Project, Tag 023Z](https://stacks.math.columbia.edu/tag/023Z)
* [Stacks Project, Tag 02VP](https://stacks.math.columbia.edu/tag/02VP)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Limits

variable {X S : Scheme.{u}}

/-- Descent data for schemes relative to a single morphism `f : X ⟶ S`: a scheme `V` over
`X` together with an isomorphism `V ×_S X ≅ X ×_S V` of schemes over `X ×_S X` satisfying the
cocycle condition. This is the one-member family case of
`AlgebraicGeometry.DescentData`. -/
@[stacks 023V "(1) descent datum for V/X/S, (2) descent datum relative to X ⟶ S",
  sga "3 IV 2.1" "descent datum"]
abbrev DescentDatum (f : X ⟶ S) :=
  DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ f)

namespace DescentDatum

variable {f : X ⟶ S}

/-- A morphism of descent data relative to `f : X ⟶ S`: a morphism of `X`-schemes commuting
with the two gluing isomorphisms. -/
@[stacks 023V "(3) morphisms of descent data relative to X ⟶ S", sga "3 IV 2.1" "partial"]
abbrev Hom (D E : DescentDatum f) := DescentData.Hom D E

/-- The scheme over `X` underlying a descent datum. -/
abbrev over (D : DescentDatum f) : Over X := D.obj ()

/-- The gluing isomorphism `φ` of a descent datum, as an isomorphism over `X ×_S X`. The
products are taken in `Over S`, where `V ×_S X` is the binary product of `V` and `X`. -/
abbrev transition (D : DescentDatum f) :
    Over.mk (prod.map (structureMap f D.over) (𝟙 (Over.mk f))) ≅
      Over.mk (prod.map (𝟙 (Over.mk f)) (structureMap f D.over)) :=
  D.gluing () ()

/-- The gluing isomorphism on the literal fibre products, `V ×_S X ≅ X ×_S V`. -/
abbrev transitionPullbackIso (D : DescentDatum f) :
    pullback (D.over.hom ≫ f) f ≅ pullback f (D.over.hom ≫ f) :=
  D.gluingPullbackIso () ()

/-- The cocycle condition on `X ×_S X ×_S X`. -/
lemma cocycle_triangle (D : DescentDatum f) :
    prod.map D.transition.hom.left (𝟙 (Over.mk f)) ≫ prodMapLastTwo D.transition.hom.left =
      prodMapFirstThird D.transition.hom.left :=
  D.cocycle () () ()

/-- A descent datum relative to `f : X ⟶ S` from the data the definition asks for: a scheme
`V` over `X`, an isomorphism `V ×_S X ≅ X ×_S V` over `X ×_S X`, and the cocycle condition. -/
abbrev mk' (V : Over X)
    (φ : Over.mk (prod.map (structureMap f V) (𝟙 (Over.mk f))) ≅
      Over.mk (prod.map (𝟙 (Over.mk f)) (structureMap f V)))
    (cocycle : prod.map φ.hom.left (𝟙 (Over.mk f)) ≫ prodMapLastTwo φ.hom.left =
      prodMapFirstThird φ.hom.left) : DescentDatum f where
  obj _ := V
  gluing _ _ := φ
  cocycle _ _ _ := cocycle

/-- The scheme of a descent datum assembled by `mk'` is the given one. -/
@[simp]
lemma mk'_over (V : Over X)
    (φ : Over.mk (prod.map (structureMap f V) (𝟙 (Over.mk f))) ≅
      Over.mk (prod.map (𝟙 (Over.mk f)) (structureMap f V)))
    (cocycle : prod.map φ.hom.left (𝟙 (Over.mk f)) ≫ prodMapLastTwo φ.hom.left =
      prodMapFirstThird φ.hom.left) : (mk' V φ cocycle).over = V := rfl

/-- The gluing isomorphism of a descent datum assembled by `mk'` is the given one. -/
@[simp]
lemma mk'_transition (V : Over X)
    (φ : Over.mk (prod.map (structureMap f V) (𝟙 (Over.mk f))) ≅
      Over.mk (prod.map (𝟙 (Over.mk f)) (structureMap f V)))
    (cocycle : prod.map φ.hom.left (𝟙 (Over.mk f)) ≫ prodMapLastTwo φ.hom.left =
      prodMapFirstThird φ.hom.left) : (mk' V φ cocycle).transition = φ := rfl

/-- The underlying `X`-scheme of a descent datum, as a functor. -/
abbrev forget (f : X ⟶ S) : DescentDatum f ⥤ Over X :=
  DescentData.evaluation (f := fun _ ↦ f) ()

/-- The canonical descent datum of a scheme over `S`, relative to `f : X ⟶ S`. -/
abbrev canonical (f : X ⟶ S) : Over S ⥤ DescentDatum f :=
  DescentData.canonicalFunctor f

/-- The canonical descent datum of a scheme over `S` is effective. -/
lemma isEffective_canonical (f : X ⟶ S) (W : Over S) :
    DescentData.IsEffective ((canonical f).obj W) :=
  (DescentData.canonicalFunctor f).obj_mem_essImage W

/-- The category of descent data relative to `f` is nonempty: it contains the canonical
descent datum of `S` over itself. -/
instance (f : X ⟶ S) : Nonempty (DescentDatum f) :=
  ⟨(canonical f).obj (Over.mk (𝟙 S))⟩

/-! ### The pullback of the gluing isomorphism along the diagonal -/

/-- The base change of `V` along the diagonal `Δ : X ⟶ X ×_S X`, viewed as the diagonal copy
of `V` inside `V ×_S X`. -/
abbrev diagLeft (f : X ⟶ S) (V : Over X) :
    (Over.map f).obj V ⟶ (Over.map f).obj V ⨯ Over.mk f :=
  prod.lift (𝟙 _) (structureMap f V)

/-- The base change of `V` along the diagonal `Δ : X ⟶ X ×_S X`, viewed as the diagonal copy
of `V` inside `X ×_S V`. -/
abbrev diagRight (f : X ⟶ S) (V : Over X) :
    (Over.map f).obj V ⟶ Over.mk f ⨯ (Over.map f).obj V :=
  prod.lift (structureMap f V) (𝟙 _)

/-- `Δ^*φ`, computed in `Over S`: restrict `φ` to the diagonal copy of `V` in `V ×_S X` and
read off its `V`-component. -/
abbrev diagHom (D : DescentDatum f) :
    (Over.map f).obj D.over ⟶ (Over.map f).obj D.over :=
  diagLeft f D.over ≫ D.transition.hom.left ≫ prod.snd

/-- `Δ^*φ` is a morphism of `X`-schemes, because `φ` lies over `X ×_S X`. -/
lemma diagHom_comp_structureMap (D : DescentDatum f) :
    D.diagHom ≫ structureMap f D.over = structureMap f D.over := by
  simp

/-- `Δ^*φ` is a morphism of `X`-schemes, on underlying schemes. -/
lemma diagHom_left_comp_hom (D : DescentDatum f) :
    D.diagHom.left ≫ D.over.hom = D.over.hom := by
  have h := congrArg Over.Hom.left D.diagHom_comp_structureMap
  rwa [Over.comp_left] at h

/-- The restriction of `φ` to the diagonal copy of `V` in `V ×_S X`, by its two
components. -/
lemma diagLeft_comp_transition (D : DescentDatum f) :
    diagLeft f D.over ≫ D.transition.hom.left =
      prod.lift (structureMap f D.over) D.diagHom := by
  apply prod.hom_ext <;> simp

/-- `Δ^*φ` is idempotent. This is the cocycle condition restricted to the diagonal of `V` in
the triple product. -/
lemma diagHom_idem (D : DescentDatum f) : D.diagHom ≫ D.diagHom = D.diagHom := by
  have key : prod.lift D.diagHom (structureMap f D.over) ≫ D.transition.hom.left ≫ prod.snd =
      D.diagHom := by
    have h := congrArg (fun g ↦ prod.lift (diagLeft f D.over) (structureMap f D.over) ≫ g ≫
      (prod.snd : _ ⟶ (Over.map f).obj D.over)) (D.cocycle () () ())
    simp only [prodMapLastTwo, prodMapFirstThird, prod.associator_hom, prod.associator_inv,
      prod.braiding_hom] at h
    simpa [prod.comp_lift, prod.comp_lift_assoc] using h
  calc D.diagHom ≫ D.diagHom
      = (D.diagHom ≫ diagLeft f D.over) ≫ D.transition.hom.left ≫ prod.snd := by
        simp only [Category.assoc]
    _ = prod.lift D.diagHom (structureMap f D.over) ≫ D.transition.hom.left ≫ prod.snd := by
        congr 1
        apply prod.hom_ext <;> simp
    _ = D.diagHom := key

/-- `Δ^*φ` has a right inverse, namely the same construction performed on `φ⁻¹`. -/
lemma diagHom_comp_inv (D : DescentDatum f) :
    D.diagHom ≫ diagRight f D.over ≫ D.transition.inv.left ≫ prod.fst =
      𝟙 ((Over.map f).obj D.over) := by
  have hdiag : D.diagHom ≫ diagRight f D.over =
      diagLeft f D.over ≫ D.transition.hom.left := by
    rw [diagLeft_comp_transition]
    apply prod.hom_ext <;> simp
  rw [← Category.assoc, hdiag]
  simp

/-- `Δ^*φ` is the identity of `V`, computed in `Over S`. -/
lemma diagHom_eq_id (D : DescentDatum f) :
    D.diagHom = 𝟙 ((Over.map f).obj D.over) :=
  calc D.diagHom
      = D.diagHom ≫ D.diagHom ≫ diagRight f D.over ≫ D.transition.inv.left ≫ prod.fst := by
        rw [D.diagHom_comp_inv, Category.comp_id]
    _ = (D.diagHom ≫ D.diagHom) ≫ diagRight f D.over ≫ D.transition.inv.left ≫ prod.fst := by
        simp only [Category.assoc]
    _ = D.diagHom ≫ diagRight f D.over ≫ D.transition.inv.left ≫ prod.fst := by
        rw [D.diagHom_idem]
    _ = 𝟙 ((Over.map f).obj D.over) := D.diagHom_comp_inv

/-- The gluing isomorphism carries the diagonal copy of `V` inside `V ×_S X` to the diagonal
copy of `V` inside `X ×_S V`. -/
lemma diagLeft_comp_transition_hom (D : DescentDatum f) :
    diagLeft f D.over ≫ D.transition.hom.left = diagRight f D.over := by
  rw [diagLeft_comp_transition, D.diagHom_eq_id]

/-- `Δ^*φ : V ⟶ V`, as a morphism of schemes over `X`. -/
def diagonalTransition (D : DescentDatum f) : D.over ⟶ D.over :=
  Over.homMk D.diagHom.left D.diagHom_left_comp_hom

/-- `Δ^*φ` as a map of `X`-schemes and `Δ^*φ` computed in `Over S` have the same underlying
morphism of schemes. -/
@[simp]
lemma diagonalTransition_left (D : DescentDatum f) :
    D.diagonalTransition.left = D.diagHom.left := rfl

/-- **`Δ^*φ` is the identity.** The pullback of the gluing isomorphism of a descent datum
along the diagonal `Δ : X ⟶ X ×_S X` is the identity of `V`. -/
theorem diagonalTransition_eq_id (D : DescentDatum f) :
    D.diagonalTransition = 𝟙 D.over := by
  ext
  rw [diagonalTransition_left, Over.id_left]
  exact congrArg Over.Hom.left D.diagHom_eq_id

end DescentDatum

end AlgebraicGeometry
