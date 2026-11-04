module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStack

/-!
# Vanishing of negative self-extensions on the field fibres, under base change

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `E` be an object of
`D(𝒪_X)`.  Condition (2) of Stacks 0DLD asks that for every field `k` and every morphism
`y : Spec(k) ⟶ Y` the negative self-extensions `Ext^i_{𝒪_{X_y}}(E_y, E_y)` vanish, where
`X_y = X ×_Y Spec(k)` is the fibre and `E_y` is the derived pullback of `E` to it.  Part (a) of
Stacks 0DLD says, in particular, that this condition survives an arbitrary base change
`V ⟶ Y`: it holds for the projection `X_V ⟶ V` and the derived pullback `E_V` of `E` to `X_V`.

The proof is the transitivity of fibres.  A point `v : Spec(k) ⟶ V` with values in a field
induces the point `Spec(k) ⟶ V ⟶ Y`, the fibre of `X_V ⟶ V` over `v` is a fibre of `X ⟶ Y` over
that point by pasting the two cartesian squares, and the derived pullback of `E_V` to it is the
derived pullback of `E` along the composite, by the composition comparison of Stacks 0D6D.

## Main definitions

* `CategoryTheory.PullbackData.pullEquivalence`: the inverse image along an isomorphism, for a
  pullback pseudofunctor datum, is an equivalence of categories.
* `AlgebraicGeometry.Space.HasNoNegativeFieldFibreExt`: **condition (2) of Stacks 0DLD** for a
  morphism of algebraic spaces and an object of the derived category of its source.

## Main results

* `AlgebraicGeometry.Space.HasNoNegativeFieldFibreExt.of_isPullback`: the condition holds at
  *every* model of the fibre, not only at the chosen fibre product.
* `AlgebraicGeometry.Space.HasNoNegativeFieldFibreExt.baseChange`: the condition is stable
  under base change along any algebraic space over the target; this is the second clause of
  part (a) of Stacks 0DLD.
* `AlgebraicGeometry.Space.ComplexesSituation.hasNoNegativeFibreExt_of_hasNoNegativeFieldFibreExt`:
  at a test scheme `T` over the base of Stacks 0DLE, this condition for the projection
  `X_T ⟶ T` gives condition (2) in the form the objects of `Complexes_{X/Y}` carry it.

## Implementation notes

A point with values in a field is a test scheme of the site whose underlying scheme is the
spectrum of a field, `AlgebraicGeometry.Stack.IsFieldObject`, with its structure morphism, as
in `AlgebraicGeometry.Space.ComplexesSituation.HasNoNegativeFibreExt`.  The fibre is the chosen
fibre product `AlgebraicGeometry.Space.baseChangeSpace`, and
`AlgebraicGeometry.Space.HasNoNegativeFieldFibreExt.of_isPullback` shows that the choice does
not matter: the derived pullback along an isomorphism of algebraic spaces is an equivalence
commuting with the shift, so it preserves and reflects the vanishing of negative
self-extensions.

## References

* [Stacks Project, Tag 0DLD](https://stacks.math.columbia.edu/tag/0DLD)
* [Stacks Project, Tag 0DLE](https://stacks.math.columbia.edu/tag/0DLE)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v₁ u₁ v₂ u₂

namespace CategoryTheory

/-- The vanishing of the morphisms from an object to its `i`-th shift transports along an
isomorphism of objects. -/
theorem subsingleton_hom_shift_of_iso {C : Type u₁} [Category.{v₁} C] [HasShift C ℤ] {M N : C}
    (e : M ≅ N) (i : ℤ) (h : Subsingleton (M ⟶ M⟦i⟧)) : Subsingleton (N ⟶ N⟦i⟧) :=
  (e.homCongr ((shiftFunctor C i).mapIso e)).symm.subsingleton

/-- A fully faithful functor commuting with the shift preserves the vanishing of the morphisms
from an object to its `i`-th shift. -/
theorem Functor.FullyFaithful.subsingleton_hom_shift {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] [HasShift C ℤ] [HasShift D ℤ] {F : C ⥤ D}
    (hF : F.FullyFaithful) [F.CommShift ℤ] (M : C) (i : ℤ) (h : Subsingleton (M ⟶ M⟦i⟧)) :
    Subsingleton (F.obj M ⟶ (F.obj M)⟦i⟧) :=
  (hF.homEquiv.trans
    ((Iso.refl (F.obj M)).homCongr ((F.commShiftIso i).app M))).symm.subsingleton

namespace PullbackData

variable {A : Type u₁} [Category.{v₁} A] {D : A → Type u₂} [∀ a, Category.{v₂} (D a)]
    (P : PullbackData A D)

/-- **The inverse image along an isomorphism is an equivalence.**  Its quasi-inverse is the
inverse image along the inverse isomorphism, and the unit and the counit are the comparisons
of the two composites with the inverse images along the identities, followed by the unit
laws. -/
def pullEquivalence {a b : A} (φ : a ≅ b) : D b ≌ D a :=
  Equivalence.mk (P.pull φ.hom) (P.pull φ.inv)
    ((P.idIso b).symm ≪≫ P.triangle φ.inv_hom_id)
    ((P.triangle φ.hom_inv_id).symm ≪≫ P.idIso a)

/-- The functor of `CategoryTheory.PullbackData.pullEquivalence` is the inverse image along the
isomorphism. -/
theorem pullEquivalence_functor {a b : A} (φ : a ≅ b) :
    (P.pullEquivalence φ).functor = P.pull φ.hom :=
  rfl

end PullbackData

end CategoryTheory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The derived pullback along a morphism of algebraic spaces commutes with the shift
(Stacks 06YY). -/
instance smallEtaleDerivedPullbackData_pull_commShift {Z W : AlgebraicSpaces B S hS}
    (g : Z ⟶ W) : ((smallEtaleDerivedPullbackData B S hS).pull g).CommShift ℤ :=
  haveI := hasDerivedModulePullbacks B S hS g
  Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback_commShift
    (smallEtaleRingedToposHom B S hS g)

/-- The derived pullback along an isomorphism of algebraic spaces preserves the vanishing of the
morphisms from an object to its `i`-th shift. -/
theorem subsingleton_hom_shift_pull_of_iso {Z W : AlgebraicSpaces B S hS} (φ : Z ≅ W)
    (M : derivedModules B S hS W) (i : ℤ) (h : Subsingleton (M ⟶ M⟦i⟧)) :
    Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull φ.hom).obj M ⟶
      (((smallEtaleDerivedPullbackData B S hS).pull φ.hom).obj M)⟦i⟧) :=
  have : ((smallEtaleDerivedPullbackData B S hS).pullEquivalence φ).functor.CommShift ℤ :=
    smallEtaleDerivedPullbackData_pull_commShift φ.hom
  ((smallEtaleDerivedPullbackData B S hS).pullEquivalence φ).fullyFaithfulFunctor
    |>.subsingleton_hom_shift M i h

variable {X Y : AlgebraicSpaces B S hS}

/-- **Condition (2) of Stacks 0DLD.**  For a morphism `f : X ⟶ Y` of algebraic spaces and an
object `E` of `D(𝒪_X)`: for every field `k` and every morphism `y : Spec(k) ⟶ Y`, the negative
self-extensions `Ext^i_{𝒪_{X_y}}(E_y, E_y)`, `i < 0`, vanish, where `X_y = X ×_Y Spec(k)` is the
fibre and `E_y` is the derived pullback of `E` along the projection `X_y ⟶ X`.

The point `y` is a test scheme `T₀` over `Y` whose underlying scheme is the spectrum of a field,
and `Ext^i(E_y, E_y)` is the group of morphisms `E_y ⟶ E_y⟦i⟧`. -/
def HasNoNegativeFieldFibreExt (f : X ⟶ Y) (E : derivedModules B S hS X) : Prop :=
  ∀ T₀ : SchemesOver Y, Stack.IsFieldObject B S hS T₀.left → ∀ i : ℤ, i < 0 →
    Subsingleton
      (((smallEtaleDerivedPullbackData B S hS).pull (baseChangeProjection f T₀)).obj E ⟶
        (((smallEtaleDerivedPullbackData B S hS).pull (baseChangeProjection f T₀)).obj E)⟦i⟧)

namespace HasNoNegativeFieldFibreExt

variable {f : X ⟶ Y} {E : derivedModules B S hS X}

/-- **The condition holds at every model of the fibre.**  If `Z` with `p : Z ⟶ X` and
`q : Z ⟶ T₀` is any cartesian square over a point `T₀ ⟶ Y` with values in a field, the negative
self-extensions of the derived pullback of `E` along `p` vanish: `Z` is isomorphic to the chosen
fibre product compatibly with the projections to `X`, and the derived pullback along that
isomorphism is an equivalence commuting with the shift. -/
theorem of_isPullback (h : HasNoNegativeFieldFibreExt f E) {T₀ : SchemesOver Y}
    (hT₀ : Stack.IsFieldObject B S hS T₀.left) {Z : AlgebraicSpaces B S hS} {p : Z ⟶ X}
    {q : Z ⟶ (schemeSpaceFunctor B S hS).obj T₀.left} (hpb : IsPullback p q f T₀.hom) (i : ℤ)
    (hi : i < 0) :
    Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull p).obj E ⟶
      (((smallEtaleDerivedPullbackData B S hS).pull p).obj E)⟦i⟧) := by
  have hT : IsPullback (baseChangeProjection f T₀) (baseChangeInclusion f T₀) f T₀.hom :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS f T₀.hom
  let φ : Z ≅ baseChangeSpace f T₀ := hpb.isoIsPullback _ _ hT
  have hφ : φ.hom ≫ baseChangeProjection f T₀ = p := hpb.isoIsPullback_hom_fst _ _ hT
  exact subsingleton_hom_shift_of_iso
    (((smallEtaleDerivedPullbackData B S hS).triangle hφ).app E).symm i
    (subsingleton_hom_shift_pull_of_iso φ _ i (h T₀ hT₀ i hi))

/-- **The second clause of part (a) of Stacks 0DLD.**  Condition (2) of Stacks 0DLD is stable
under base change: if it holds for `f : X ⟶ Y` and `E`, then for every algebraic space `V` over
`Y` it holds for the projection `X_V ⟶ V` and the derived pullback `E_V` of `E` along the
projection `X_V ⟶ X`.

A point `v : Spec(k) ⟶ V` induces the point `Spec(k) ⟶ V ⟶ Y`; the fibre of `X_V ⟶ V` over `v`
is a fibre of `f` over it by pasting the two cartesian squares, and the derived pullback of
`E_V` to it is the derived pullback of `E` along the composite. -/
theorem baseChange (h : HasNoNegativeFieldFibreExt f E) (V : Over Y) :
    HasNoNegativeFieldFibreExt (overInclusion f V)
      (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj E) := by
  intro T₀ hT₀ i hi
  let T₁ : SchemesOver Y := CostructuredArrow.mk (T₀.hom ≫ V.hom)
  have hpb : IsPullback (baseChangeProjection (overInclusion f V) T₀ ≫ overProjection f V)
      (baseChangeInclusion (overInclusion f V) T₀) f T₁.hom :=
    (AlgebraicSpaces.isPullback_fiberProduct B S hS (overInclusion f V) T₀.hom).paste_horiz
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f V.hom)
  exact subsingleton_hom_shift_of_iso
    (((smallEtaleDerivedPullbackData B S hS).compIso
      (baseChangeProjection (overInclusion f V) T₀) (overProjection f V)).app E) i
    (h.of_isPullback (T₀ := T₁) hT₀ hpb i hi)

end HasNoNegativeFieldFibreExt

/-- At a test scheme `T` over the base of Stacks 0DLE, condition (2) of Stacks 0DLD for the
projection `X_T ⟶ T` gives the form of that condition which the objects of `Complexes_{X/Y}`
carry, `AlgebraicGeometry.Space.ComplexesSituation.HasNoNegativeFibreExt`: a point `y : T₀ ⟶ T`
with values in a field is a point of `T`, and the base change `X_{T₀}` with the induced morphism
`X_{T₀} ⟶ X_T` is a model of the fibre of `X_T ⟶ T` over it. -/
theorem ComplexesSituation.hasNoNegativeFibreExt_of_hasNoNegativeFieldFibreExt
    (D : ComplexesSituation B S hS) (T : SchemesOver D.Y) (E : derivedModules B S hS (D.space T))
    (h : HasNoNegativeFieldFibreExt (D.projection T) E) : D.HasNoNegativeFibreExt T E := by
  intro T₀ hT₀ y i hi
  exact h.of_isPullback (T₀ := CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map y.left))
    hT₀ (isPullback_baseChangeMap D.f y) i hi

end AlgebraicGeometry.Space
