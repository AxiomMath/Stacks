module

public import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Tactic.Ring
import StacksFrontier.CategoryTheory.Triangulated.Elementary
public import StacksFrontier.CategoryTheory.Triangulated.Quotient
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Admissible subcategories of a triangulated category

Let `C` be a pretriangulated category and let `A : ObjectProperty C` be a property of its objects,
viewed as the full subcategory of `C` it spans. Its right orthogonal `A.rightOrthogonal` is the
property of objects `Y` such that every morphism `X ⟶ Y` with `A X` vanishes, and dually for the
left orthogonal `A.leftOrthogonal`. Both are stable under retracts, hence saturated (thick) and
strictly full, in any category with zero morphisms; over a pretriangulated `C` and a
shift-invariant `A` they are moreover triangulated subcategories, which is Mathlib's instance for
`ObjectProperty.IsTriangulated`.

The subcategory `A` is *right admissible* when the inclusion `A.ι : A.FullSubcategory ⥤ C` has a
right adjoint, and *left admissible* when it has a left adjoint. Writing `P ⋆ Q` for the extension
product — the objects `X` fitting in a distinguished triangle `A' ⟶ X ⟶ B' ⟶ A'⟦1⟧` with `A' ∈ P`
and `B' ∈ Q` — the two conditions are decompositions of the ambient category:

* `A.ι` has a right adjoint if and only if `A ⋆ Aᗮ = ⊤`, and then `A` is saturated with
  `A.isoClosure = ᗮ(Aᗮ)`;
* `B.ι` has a left adjoint if and only if `ᗮB ⋆ B = ⊤`, and then `B` is saturated with
  `B.isoClosure = (ᗮB)ᗮ`.

Both rest on the same elementary observation: for a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧`,
the object `X₃` lies in `A.rightOrthogonal` exactly when `Hom(W, X₁) ⟶ Hom(W, X₂)` is bijective for
every `W` satisfying `A`. One direction produces, from an adjunction, a triangle on its counit
whose third object is orthogonal; the other feeds the bijections to the universal arrow criterion
and gets the adjoint functor and the adjunction at once.

Semiorthogonality also makes the extension product itself well behaved: if `B ≤ Aᗮ` then a
triangle with first object in `B` and third in `A` has vanishing connecting map, hence splits, so
`B ⋆ A ≤ A ⋆ B`, and associativity of `⋆` turns that commutation into idempotence of `A ⋆ B`,
which *is* the two-out-of-three property. Consequently `A ⋆ B` is a triangulated subcategory of
`C`, and in particular so are `A ⋆ Aᗮ` and `ᗮB ⋆ B`.

Finally, for a semiorthogonal pair `(A, B)` covering `C` — no nonzero morphism from `A` to `B`,
and `A ⋆ B = ⊤` — the three descriptions of the situation agree: `A` is right admissible with
`B = Aᗮ`, `B` is left admissible with `A = ᗮB`, and `A ≤ ᗮB` with `A ⋆ B = ⊤`. When they hold,
`A` is the Verdier quotient of `C` by `B` and `B` is the Verdier quotient of `C` by `A`: for every
localization `L : C ⥤ Q` of `C` at `B.trW` the composite `A.ι ⋙ L` is an equivalence, and a right
adjoint of `A.ι` factors as `L ⋙ G`.

## Main results

* `CategoryTheory.ObjectProperty.isStableUnderRetracts_rightOrthogonal_and_leftOrthogonal`: the
  two orthogonals of a property of objects are stable under retracts, hence saturated.
* `CategoryTheory.ObjectProperty.isTriangulated_extensionProduct_of_le_rightOrthogonal`: for
  triangulated `A`, `B` with `B ≤ A.rightOrthogonal`, the extension product `A ⋆ B` is a
  triangulated subcategory.
* `CategoryTheory.ObjectProperty.isTriangulated_extensionProduct_leftOrthogonal_self`: for a
  triangulated `B`, the extension product `ᗮB ⋆ B` is a triangulated subcategory.
* `ObjectProperty.isLeftAdjoint_ι_iff_extensionProduct_rightOrthogonal_eq_top_and_isSaturated`:
  the inclusion of a shift-invariant `A` has a right adjoint if and only if `A ⋆ Aᗮ = ⊤`, and then
  `A` is saturated and `A.isoClosure = ᗮ(Aᗮ)`.
* `isRightAdjoint_ι_iff_extensionProduct_leftOrthogonal_self_eq_top_and_isSaturated`, in the same
  namespace: the inclusion of a shift-invariant `B` has a left adjoint if and only if
  `ᗮB ⋆ B = ⊤`, and then `B` is saturated and `B.isoClosure = (ᗮB)ᗮ`.
* `tfae_isRightAdmissible_isLeftAdmissible_extensionProduct_and_isEquivalence_ι_comp`, in the same
  namespace: the three descriptions of a semiorthogonal decomposition are equivalent, and each
  factor is a Verdier quotient of `C` by the other, with the adjoints factoring through it.

## Implementation notes

The hypotheses are those the arguments use, which is less than the source assumes. Stability of the
orthogonals under retracts needs only zero morphisms — no additive or triangulated structure — and
is formally stronger than the closure under direct summands of the source, a direct summand being a
retract; together with closure under isomorphisms it gives `ObjectProperty.IsSaturated`, the
saturation of the source's Definition 05RB. The two adjunction criteria use of the ambient category
only `Pretriangulated C` and of the subcategory only `IsStableUnderShift ℤ`, the octahedron axiom
entering nowhere; the source's case of a triangulated subcategory of a triangulated category is
recovered from `[A.IsTriangulated]`, which supplies that instance. For the same reason the
statements about extension products are made for a semiorthogonal pair `(A, B)` with
`B ≤ A.rightOrthogonal` rather than for `B = Aᗮ`, the source's instantiation being the case
`le_rfl`; and `A ≤ B.leftOrthogonal` and `B ≤ A.rightOrthogonal` are literally the same condition,
so no passage to the opposite category occurs anywhere below.

Strict fullness is never assumed where it can be avoided: a property of objects spans a full
subcategory by construction, and the identifications of the source are stated for `A.isoClosure`,
which `ObjectProperty.isoClosure_eq_self` turns into the source's own equalities for a strictly
full `A`. `ObjectProperty.IsSaturated` is itself a condition on `A.isoClosure`, so it needs no
strictification either.

Two other assertions of the source cost nothing and are therefore not restated. The strict
fullness of an orthogonal, `ObjectProperty.IsClosedUnderIsomorphisms`, and the triangulated
structure of an orthogonal of a shift-invariant property, `ObjectProperty.IsTriangulated`, are
Mathlib instances. And the closure of a triangulated subcategory under direct sums follows from
`ObjectProperty.IsClosedUnderBinaryProducts`, available by instance resolution for any
triangulated property closed under isomorphisms, together with `X₁ ⊞ X₂ ≅ X₁ ⨯ X₂`.

For the two adjunction criteria the adjoint functor is not built by hand: the families of
bijections `Hom(W, A') = Hom(W, X)`, resp. `Hom(B', W) = Hom(X, W)`, are fed to the universal
arrow criteria `isLeftAdjoint_of_bijective_postcomp` and `isRightAdjoint_of_bijective_precomp`
below, which package `Adjunction.adjunctionOfEquivRight` and `Adjunction.adjunctionOfEquivLeft`, so
that no naturality is checked twice.

## References

* [Stacks project, Tag 0FXC](https://stacks.math.columbia.edu/tag/0FXC)
* [Stacks project, Tag 0CQR](https://stacks.math.columbia.edu/tag/0CQR)
* [Stacks project, Tag 0H0N](https://stacks.math.columbia.edu/tag/0H0N)
* [Stacks project, Tag 0CQS](https://stacks.math.columbia.edu/tag/0CQS)
* [Stacks project, Tag 0CQT](https://stacks.math.columbia.edu/tag/0CQT)
* [Stacks project, Tag 0H0P](https://stacks.math.columbia.edu/tag/0H0P)
* [Stacks project, Tag 0CQQ](https://stacks.math.columbia.edu/tag/0CQQ)
* [Stacks project, Tag 0H0M](https://stacks.math.columbia.edu/tag/0H0M)
* [Stacks project, Tag 0FXB](https://stacks.math.columbia.edu/tag/0FXB)
* [Stacks project, Tag 0FXD](https://stacks.math.columbia.edu/tag/0FXD)
* [Stacks project, Tag 05RB](https://stacks.math.columbia.edu/tag/05RB)
* [Stacks project, Tag 05QT](https://stacks.math.columbia.edu/tag/05QT)
* [Stacks project, Tag 05R0](https://stacks.math.columbia.edu/tag/05R0)
* [Stacks project, Tag 0FX1](https://stacks.math.columbia.edu/tag/0FX1)
-/

@[expose] public section

universe w' w v v' u u'

namespace CategoryTheory.ObjectProperty

open Limits Pretriangulated

/-! ### The orthogonals of a property of objects -/

section Orthogonal

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- The right orthogonal of a property of objects of a category with zero morphisms descends
along monomorphisms: if every morphism into `Y` from an object satisfying `P` vanishes and
`g : X ⟶ Y` is a monomorphism, then every morphism into `X` from an object satisfying `P`
vanishes. -/
private lemma rightOrthogonal_of_mono (P : ObjectProperty C) {X Y : C} (g : X ⟶ Y) [Mono g]
    (hY : P.rightOrthogonal Y) : P.rightOrthogonal X :=
  fun _ f hA ↦ zero_of_comp_mono g (hY (f ≫ g) hA)

/-- The left orthogonal of a property of objects of a category with zero morphisms descends
along epimorphisms: if every morphism out of `Y` into an object satisfying `P` vanishes and
`g : Y ⟶ X` is an epimorphism, then every morphism out of `X` into an object satisfying `P`
vanishes. -/
private lemma leftOrthogonal_of_epi (P : ObjectProperty C) {X Y : C} (g : Y ⟶ X) [Epi g]
    (hY : P.leftOrthogonal Y) : P.leftOrthogonal X :=
  fun _ f hB ↦ zero_of_epi_comp g (hY (g ≫ f) hB)

/-- Let `C` be a category with zero morphisms and `P : ObjectProperty C` a property of its
objects. Then both the right orthogonal `P.rightOrthogonal` and the left orthogonal
`P.leftOrthogonal` are stable under retracts; in particular they are saturated, i.e. thick, and
strictly full subcategories of `C`. -/
@[stacks 0FXC, sga "4½ Etat_0 2.6.2" "thickness"]
theorem isStableUnderRetracts_rightOrthogonal_and_leftOrthogonal (P : ObjectProperty C) :
    P.rightOrthogonal.IsStableUnderRetracts ∧ P.leftOrthogonal.IsStableUnderRetracts :=
  ⟨⟨fun h hY ↦ rightOrthogonal_of_mono P h.i hY⟩, ⟨fun h hY ↦ leftOrthogonal_of_epi P h.r hY⟩⟩

/-- If no nonzero morphism goes from `A` to `B`, then `B` is contained in the right orthogonal
of `A`. -/
private lemma le_rightOrthogonal_of_le_leftOrthogonal {A B : ObjectProperty C}
    (hAB : A ≤ B.leftOrthogonal) : B ≤ A.rightOrthogonal :=
  fun _ hY _ f hX ↦ hAB _ hX f hY

end Orthogonal

/-! ### The universal arrow criteria -/

section UniversalArrow

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- The universal arrow criterion for the existence of a right adjoint: if for every object `X`
of `C` there is an object `G X` of `D` and a morphism `u X : F.obj (G X) ⟶ X` through which every
morphism `F.obj S ⟶ X` factors uniquely, then `F` has a right adjoint. -/
private lemma isLeftAdjoint_of_bijective_postcomp (F : D ⥤ C) (G : C → D)
    (u : ∀ X : C, F.obj (G X) ⟶ X)
    (hu : ∀ (X : C) (S : D), Function.Bijective fun k : S ⟶ G X ↦ F.map k ≫ u X) :
    F.IsLeftAdjoint := by
  let e : ∀ (S : D) (X : C), (F.obj S ⟶ X) ≃ (S ⟶ G X) := fun S X ↦
    (Equiv.ofBijective _ (hu X S)).symm
  have hkey : ∀ (S : D) (X : C) (k : F.obj S ⟶ X), F.map (e S X k) ≫ u X = k := fun S X k ↦
    (Equiv.ofBijective _ (hu X S)).apply_symm_apply k
  refine ⟨_, ⟨Adjunction.adjunctionOfEquivRight e (fun S' S X φ k ↦ (hu X S').injective ?_)⟩⟩
  rw [hkey, F.map_comp, Category.assoc, hkey]

/-- The universal arrow criterion for the existence of a left adjoint: if for every object `X`
of `C` there is an object `F X` of `D` and a morphism `u X : X ⟶ G.obj (F X)` through which every
morphism `X ⟶ G.obj S` factors uniquely, then `G` has a left adjoint. -/
private lemma isRightAdjoint_of_bijective_precomp (G : D ⥤ C) (F : C → D)
    (u : ∀ X : C, X ⟶ G.obj (F X))
    (hu : ∀ (X : C) (S : D), Function.Bijective fun k : F X ⟶ S ↦ u X ≫ G.map k) :
    G.IsRightAdjoint :=
  ⟨_, ⟨Adjunction.adjunctionOfEquivLeft (fun X S ↦ Equiv.ofBijective _ (hu X S))
    (fun X Y Y' g h ↦ by simp [Equiv.ofBijective])⟩⟩

/-- The unit of an adjunction with fully faithful right adjoint is a universal arrow into the
image of that adjoint: pre-composition with `adj.unit.app X` is a bijection
`Hom(R L X, R S) = Hom(X, R S)`. -/
private lemma bijective_precomp_unit {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (hR : R.FullyFaithful) (X : C) (S : D) :
    Function.Bijective fun g : R.obj (L.obj X) ⟶ R.obj S ↦ adj.unit.app X ≫ g := by
  have h : (fun g : R.obj (L.obj X) ⟶ R.obj S ↦ adj.unit.app X ≫ g) =
      adj.homEquiv X S ∘ hR.homEquiv.symm := by
    funext g
    simp [Adjunction.homEquiv_unit]
  rw [h]
  exact (adj.homEquiv X S).bijective.comp hR.homEquiv.symm.bijective

/-- The composite of the inclusion of a property of objects with a functor `L` is an equivalence
as soon as `L` is bijective on morphisms between objects of the property and the composite is
essentially surjective. -/
private lemma isEquivalence_ι_comp_of_map_bijective {P : ObjectProperty C} (L : C ⥤ D)
    (hL : ∀ X Y : P.FullSubcategory, Function.Bijective (L.map : (X.obj ⟶ Y.obj) → _))
    (hs : (P.ι ⋙ L).EssSurj) : (P.ι ⋙ L).IsEquivalence := by
  refine ⟨⟨fun {X Y} f g hfg ↦ ObjectProperty.hom_ext _ ((hL X Y).1 hfg)⟩, ⟨fun {X Y} f ↦ ?_⟩, hs⟩
  obtain ⟨a, ha⟩ := (hL X Y).2 f
  exact ⟨⟨a⟩, ha⟩

end UniversalArrow

section Transport

variable {C : Type u} [Category.{v} C]

/-- Bijectivity of post-composition with a morphism transports along bijections of hom-sets that
are compatible with the two morphisms. -/
private lemma bijective_postcomp_of_bijective {D : Type u'} [Category.{v'} D]
    {P X Y : C} {P' X' Y' : D} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (a : (P ⟶ X) ≃ (P' ⟶ X')) (b : (P ⟶ Y) ≃ (P' ⟶ Y'))
    (hab : ∀ g : P ⟶ X, a g ≫ f' = b (g ≫ f))
    (h : Function.Bijective fun g : P ⟶ X ↦ g ≫ f) :
    Function.Bijective fun g : P' ⟶ X' ↦ g ≫ f' := by
  have heq : (fun g : P' ⟶ X' ↦ g ≫ f') = b ∘ (fun g : P ⟶ X ↦ g ≫ f) ∘ a.symm := by
    funext g
    simpa using hab (a.symm g)
  rw [heq]
  exact b.bijective.comp (h.comp a.symm.bijective)

variable [HasShift C ℤ]

/-- If post-composition with `f : X ⟶ Y` is bijective on morphisms out of `P⟦-n⟧`, then
post-composition with `f⟦n⟧'` is bijective on morphisms out of `P`. -/
private lemma bijective_postcomp_shift {P X Y : C} (f : X ⟶ Y) (n : ℤ)
    (h : Function.Bijective fun g : P⟦-n⟧ ⟶ X ↦ g ≫ f) :
    Function.Bijective fun g : P ⟶ X⟦n⟧ ↦ g ≫ f⟦n⟧' :=
  bijective_postcomp_of_bijective
    ((shiftEquiv' C (-n) n (neg_add_cancel n)).toAdjunction.homEquiv P X)
    ((shiftEquiv' C (-n) n (neg_add_cancel n)).toAdjunction.homEquiv P Y)
    (fun g ↦ ((shiftEquiv' C (-n) n (neg_add_cancel n)).toAdjunction.homEquiv_naturality_right
      g f).symm) h

end Transport

/-! ### Right and left admissible subcategories -/

section Admissible

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A property `A` of the objects of a pretriangulated category `C` is *right admissible* if it is
strictly full (closed under isomorphisms) and triangulated, and the inclusion
`A.ι : A.FullSubcategory ⥤ C` has a right adjoint. By [Stacks, Tag 0CQS] the last condition holds
if and only if every object `X` of `C` fits in a distinguished triangle `A' ⟶ X ⟶ B ⟶ A'⟦1⟧` with
`A'` satisfying `A` and `B` in the right orthogonal of `A`, and it then forces `A = ᗮ(Aᗮ)`. -/
@[stacks 0FXD]
public class IsRightAdmissible (A : ObjectProperty C) : Prop extends
  A.IsClosedUnderIsomorphisms, A.IsTriangulated, A.ι.IsLeftAdjoint

/-- A property `A` of the objects of a pretriangulated category `C` is *left admissible* if it is
strictly full (closed under isomorphisms) and triangulated, and the inclusion
`A.ι : A.FullSubcategory ⥤ C` has a left adjoint. By [Stacks, Tag 0CQT] the last condition holds
if and only if every object `X` of `C` fits in a distinguished triangle `A' ⟶ X ⟶ B ⟶ A'⟦1⟧` with
`A'` in the left orthogonal of `A` and `B` satisfying `A`, and it then forces `A = (ᗮA)ᗮ`. -/
@[stacks 0FXD]
public class IsLeftAdmissible (A : ObjectProperty C) : Prop extends
  A.IsClosedUnderIsomorphisms, A.IsTriangulated, A.ι.IsRightAdjoint

/-- A property `A` of the objects of a pretriangulated category `C` is *two-sided admissible* if
it is both right and left admissible, i.e. `A` is a strictly full triangulated subcategory whose
inclusion `A.ι : A.FullSubcategory ⥤ C` has both a right and a left adjoint. -/
@[stacks 0FXD]
public class IsTwoSidedAdmissible (A : ObjectProperty C) : Prop extends
  A.IsRightAdmissible, A.IsLeftAdmissible

section RightOrthogonal

variable (A : ObjectProperty C) [A.IsStableUnderShift ℤ] {T : Triangle C}

/-- **[Stacks, Tag 0CQQ]**, first implication. If the third object of a distinguished triangle
lies in the right orthogonal of a shift-invariant `A`, then post-composition with the first
morphism of the triangle is bijective on morphisms out of any object satisfying `A`. -/
private lemma bijective_postcomp_mor₁_of_rightOrthogonal (hT : T ∈ distTriang C)
    (hT₃ : A.rightOrthogonal T.obj₃) {W : C} (hW : A W) :
    Function.Bijective fun g : W ⟶ T.obj₁ ↦ g ≫ T.mor₁ := by
  have hker : ∀ g : W ⟶ T.obj₁, g ≫ T.mor₁ = 0 → g = 0 := by
    intro g hg
    obtain ⟨g', hg'⟩ := Triangle.coyoneda_exact₂ T.invRotate (inv_rot_of_distTriang T hT) g hg
    have h₃ : A.rightOrthogonal (T.obj₃⟦(-1 : ℤ)⟧) := A.rightOrthogonal.le_shift (-1) _ hT₃
    have hg'' : g' = 0 := h₃ g' hW
    rw [hg', hg'']
    exact zero_comp
  refine ⟨fun g₁ g₂ hg ↦ ?_, fun k ↦ ?_⟩
  · have hg' : g₁ ≫ T.mor₁ = g₂ ≫ T.mor₁ := hg
    rw [← sub_eq_zero]
    exact hker _ (by rw [Preadditive.sub_comp, hg', sub_self])
  · obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ T hT k (hT₃ (k ≫ T.mor₂) hW)
    exact ⟨g, hg.symm⟩

/-- **[Stacks, Tag 0CQQ]**, converse implication. If post-composition with the first morphism of
a distinguished triangle is bijective on morphisms out of every object satisfying a
shift-invariant `A`, then the third object of the triangle lies in the right orthogonal of `A`. -/
private lemma rightOrthogonal_obj₃_of_bijective (hT : T ∈ distTriang C)
    (h : ∀ ⦃W : C⦄, A W → Function.Bijective fun g : W ⟶ T.obj₁ ↦ g ≫ T.mor₁) :
    A.rightOrthogonal T.obj₃ := by
  intro W k hW
  have hW' : A (W⟦(-1 : ℤ)⟧) := A.le_shift (-1) W hW
  have h₁ : k ≫ T.mor₃ = 0 := by
    refine (bijective_postcomp_shift T.mor₁ 1 (h hW')).1 ?_
    dsimp only
    rw [zero_comp, Category.assoc, comp_distTriang_mor_zero₃₁ T hT, comp_zero]
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₃ T hT k h₁
  obtain ⟨g', hg'⟩ := (h hW).2 g
  dsimp only at hg'
  rw [hg, ← hg', Category.assoc, comp_distTriang_mor_zero₁₂ T hT, comp_zero]

end RightOrthogonal

/-- Let `C` be a pretriangulated category and let `A : ObjectProperty C` be invariant under all
shifts, for instance a triangulated subcategory of `C`. Then the inclusion
`A.ι : A.FullSubcategory ⥤ C` has a right adjoint if and only if every object `X` of `C` fits in
a distinguished triangle `A' ⟶ X ⟶ B ⟶ A'⟦1⟧` with `A'` satisfying `A` and `B` in the right
orthogonal of `A`, i.e. if and only if `A.extensionProduct A.rightOrthogonal = ⊤`; and in that
case `A` is saturated, i.e. thick ([Stacks, Tag 05RB]), and the objects isomorphic to an object
satisfying `A` are exactly the objects of the left orthogonal of `A.rightOrthogonal`, so a
strictly full such `A` satisfies `A = ᗮ(Aᗮ)`. -/
@[stacks 0CQS]
theorem isLeftAdjoint_ι_iff_extensionProduct_rightOrthogonal_eq_top_and_isSaturated
    (A : ObjectProperty C) [A.IsStableUnderShift ℤ] :
    (A.ι.IsLeftAdjoint ↔ A.extensionProduct A.rightOrthogonal = ⊤) ∧
      (A.extensionProduct A.rightOrthogonal = ⊤ →
        A.IsSaturated ∧ A.isoClosure = A.rightOrthogonal.leftOrthogonal) := by
  have hex : A.extensionProduct A.rightOrthogonal = ⊤ → ∀ X : C,
      ∃ (Y Z : C) (a : Y ⟶ X) (b : X ⟶ Z) (c : Z ⟶ Y⟦(1 : ℤ)⟧),
        Triangle.mk a b c ∈ distTriang C ∧ A Y ∧ A.rightOrthogonal Z :=
    fun htop X ↦ le_of_eq htop.symm X trivial
  constructor
  · constructor
    · -- (1) ⟹ (2): extend the counit at `X` to a distinguished triangle.
      intro _
      have adj := Adjunction.ofIsLeftAdjoint A.ι
      rw [eq_top_iff]
      intro X _
      obtain ⟨B, g, h, hT⟩ := distinguished_cocone_triangle (adj.counit.app X)
      refine ⟨_, B, adj.counit.app X, g, h, hT, (A.ι.rightAdjoint.obj X).property,
        rightOrthogonal_obj₃_of_bijective A hT (fun W hW ↦ ?_)⟩
      exact ((A.fullyFaithfulι.homEquiv (X := (⟨W, hW⟩ : A.FullSubcategory))
        (Y := A.ι.rightAdjoint.obj X)).symm.trans (adj.homEquiv _ X).symm).bijective
    · -- (2) ⟹ (1): the first object of the triangle is the value of the right adjoint.
      intro htop
      choose Y Z a b c hT hY hZ using hex htop
      refine isLeftAdjoint_of_bijective_postcomp A.ι (fun X ↦ ⟨Y X, hY X⟩) a (fun X S ↦ ?_)
      exact (bijective_postcomp_mor₁_of_rightOrthogonal A (hT X) (hZ X) S.property).comp
        A.fullyFaithfulι.homEquiv.bijective
  · -- The final statement.
    intro htop
    have hiso : A.isoClosure = A.rightOrthogonal.leftOrthogonal := by
      refine le_antisymm ((isoClosure_le_iff _ _).2 (fun X hX W f hW ↦ hW f hX)) (fun X hX ↦ ?_)
      obtain ⟨Y, Z, u, v, w, hT, hY, hZ⟩ := hex htop X
      set T : Triangle C := Triangle.mk u v w
      -- `X ⟶ Z` is zero because `Z` lies in `A.rightOrthogonal`.
      have hv : T.mor₂ = 0 := hX v hZ
      -- so the double rotation of `T` has vanishing connecting morphism, hence splits.
      have hT'' : T.rotate.rotate ∈ distTriang C :=
        rot_of_distTriang _ (rot_of_distTriang _ hT)
      have hzero : T.rotate.rotate.mor₃ = 0 := by
        change -(T.mor₂⟦(1 : ℤ)⟧') = 0
        rw [hv, Functor.map_zero, neg_zero]
      have := T.rotate.rotate.epi₂ hT'' hzero
      have := isSplitEpi_of_epi T.rotate.rotate.mor₂
      have hd : IsIso (biprod.desc T.rotate.rotate.mor₁ (section_ T.rotate.rotate.mor₂)) :=
        isIso_biprod_desc_of_distTriang T.rotate.rotate hT'' _ (IsSplitEpi.id _)
      -- the retraction `Y⟦1⟧ ⟶ Z` vanishes, since `Y⟦1⟧` satisfies `A` and `Z` is orthogonal
      have hfst : inv (biprod.desc T.rotate.rotate.mor₁ (section_ T.rotate.rotate.mor₂)) ≫
          biprod.fst = 0 := hZ _ (A.le_shift 1 Y hY)
      have hZzero : IsZero T.obj₃ := by
        have hid : (𝟙 T.rotate.rotate.obj₁) = 0 := by
          have hassoc := IsIso.hom_inv_id_assoc
            (biprod.desc T.rotate.rotate.mor₁ (section_ T.rotate.rotate.mor₂))
            (biprod.fst (X := T.rotate.rotate.obj₁) (Y := T.rotate.rotate.obj₃))
          rw [← biprod.inl_fst (X := T.rotate.rotate.obj₁) (Y := T.rotate.rotate.obj₃), ← hassoc,
            ← Category.assoc, biprod.inl_desc, hfst, comp_zero]
        exact (IsZero.iff_id_eq_zero _).2 hid
      have : IsIso T.mor₁ := (T.isZero₃_iff_isIso₁ hT).1 hZzero
      exact ⟨Y, hY, ⟨(asIso T.mor₁).symm⟩⟩
    have := (isStableUnderRetracts_rightOrthogonal_and_leftOrthogonal A.rightOrthogonal).2
    refine ⟨⟨fun hbip ↦ ?_, fun hbip ↦ ?_⟩, hiso⟩ <;> rw [hiso] at hbip ⊢
    · exact prop_of_retract _ ⟨biprod.inl, biprod.fst, by simp⟩ hbip
    · exact prop_of_retract _ ⟨biprod.inr, biprod.snd, by simp⟩ hbip

section LeftOrthogonal

variable (B : ObjectProperty C)

/-- Condition (2) of [Stacks, Tag 0CQT], unfolded: if `B.leftOrthogonal.extensionProduct B` is
`⊤`, then every object `X` of `C` is the second object of a distinguished triangle whose first
object lies in `B.leftOrthogonal` and whose third object satisfies `B`. -/
private lemma exists_distTriang_of_extensionProduct_eq_top
    (htop : B.leftOrthogonal.extensionProduct B = ⊤) (X : C) :
    ∃ (A Z : C) (u : A ⟶ X) (v : X ⟶ Z) (w : Z ⟶ A⟦(1 : ℤ)⟧),
      Triangle.mk u v w ∈ distTriang C ∧ B.leftOrthogonal A ∧ B Z :=
  (B.leftOrthogonal.extensionProduct_iff B X).1 (htop.ge X trivial)

variable [B.IsStableUnderShift ℤ] {T : Triangle C}

/-- **[Stacks, Tag 0H0M]**, the dual of [Stacks, Tag 0CQQ], first implication. If the first
object of a distinguished triangle lies in the left orthogonal of a shift-invariant `B`, then
pre-composition with the second morphism of the triangle is bijective on morphisms into any
object satisfying `B`. -/
private lemma bijective_precomp_mor₂_of_leftOrthogonal (hT : T ∈ distTriang C)
    (hT₁ : B.leftOrthogonal T.obj₁) {W : C} (hW : B W) :
    Function.Bijective fun g : T.obj₃ ⟶ W ↦ T.mor₂ ≫ g := by
  have hW' : B.leftOrthogonal.trW.isLocal W := by
    rw [isLocal_trW]
    exact le_rightOrthogonal_leftOrthogonal B W hW
  exact hW' T.mor₂ (trW.mk' _ hT hT₁)

/-- **[Stacks, Tag 0H0M]**, the dual of [Stacks, Tag 0CQQ], converse implication. If
pre-composition with the second morphism of a distinguished triangle is bijective on morphisms
into every object satisfying a shift-invariant `B`, then the first object of the triangle lies in
the left orthogonal of `B`. -/
private lemma leftOrthogonal_obj₁_of_bijective (hT : T ∈ distTriang C)
    (h : ∀ ⦃W : C⦄, B W → Function.Bijective fun g : T.obj₃ ⟶ W ↦ T.mor₂ ≫ g) :
    B.leftOrthogonal T.obj₁ := by
  intro W k hW
  have h₁ : T.mor₃ ≫ k⟦(1 : ℤ)⟧' = 0 := (h (B.le_shift 1 W hW)).1 (by
    dsimp only
    rw [comp_zero, ← Category.assoc, comp_distTriang_mor_zero₂₃ T hT, zero_comp])
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ T.rotate.rotate
    (rot_of_distTriang _ (rot_of_distTriang _ hT)) (k⟦(1 : ℤ)⟧') h₁
  have hbij : Function.Bijective fun g : T.obj₃⟦(1 : ℤ)⟧ ⟶ W⟦(1 : ℤ)⟧ ↦ T.mor₂⟦(1 : ℤ)⟧' ≫ g :=
    (Adjunction.map_comp_bijective_iff (shiftEquiv C (1 : ℤ)).toAdjunction T.mor₂ _).2
      (h (B.le_shift (-1) _ (B.le_shift 1 W hW)))
  obtain ⟨g', hg'⟩ := hbij.2 g
  refine (shiftFunctor C (1 : ℤ)).map_injective ?_
  rw [Functor.map_zero, hg, ← hg']
  change (-(T.mor₁⟦(1 : ℤ)⟧')) ≫ T.mor₂⟦(1 : ℤ)⟧' ≫ g' = 0
  rw [Preadditive.neg_comp, ← Functor.map_comp_assoc, comp_distTriang_mor_zero₁₂ T hT,
    Functor.map_zero, zero_comp, neg_zero]

/-- The heart of the last assertion of [Stacks, Tag 0CQT]. In a distinguished triangle
`A ⟶ X ⟶ B' ⟶ A⟦1⟧` with `A` in `B.leftOrthogonal`, `B'` satisfying `B` and `X` in the right
orthogonal of `B.leftOrthogonal`, the object `A` is zero: the morphism `A ⟶ X` vanishes by
orthogonality, so `B' ⟶ A⟦1⟧` is a split epimorphism, and its section vanishes because it goes
from `A⟦1⟧`, which is in `B.leftOrthogonal`, to `B'`, which satisfies `B`. -/
private lemma isZero_obj₁_of_rightOrthogonal_obj₂ (hT : T ∈ distTriang C)
    (hT₁ : B.leftOrthogonal T.obj₁) (hT₂ : B.leftOrthogonal.rightOrthogonal T.obj₂)
    (hT₃ : B T.obj₃) : IsZero T.obj₁ := by
  have hmor₁ : T.mor₁ = 0 := hT₂ T.mor₁ hT₁
  have : Epi T.mor₃ := T.rotate.epi₂ (rot_of_distTriang _ hT) (by
    change -(T.mor₁⟦(1 : ℤ)⟧') = 0
    rw [hmor₁, Functor.map_zero, neg_zero])
  have := isSplitEpi_of_epi T.mor₃
  have hsec : section_ T.mor₃ = 0 := B.leftOrthogonal.le_shift 1 _ hT₁ _ hT₃
  have hzero : IsZero (T.obj₁⟦(1 : ℤ)⟧) := (IsZero.iff_id_eq_zero _).2 (by
    rw [← IsSplitEpi.id T.mor₃, hsec, zero_comp])
  exact (T.isZero₁_iff hT).2 ⟨hmor₁, hzero.eq_zero_of_tgt _⟩

end LeftOrthogonal

/-- Let `C` be a pretriangulated category and let `B : ObjectProperty C` be invariant under all
shifts, for instance a triangulated subcategory of `C`. Then the inclusion
`B.ι : B.FullSubcategory ⥤ C` has a left adjoint if and only if every object `X` of `C` fits in a
distinguished triangle `A ⟶ X ⟶ B' ⟶ A⟦1⟧` with `A` in the left orthogonal of `B` and `B'`
satisfying `B`, i.e. if and only if `B.leftOrthogonal.extensionProduct B = ⊤`; and in that case
`B` is saturated, i.e. thick ([Stacks, Tag 05RB]), and the objects isomorphic to an object
satisfying `B` are exactly the objects of the right orthogonal of `B.leftOrthogonal`, so a
strictly full such `B` satisfies `B = (ᗮB)ᗮ`. -/
@[stacks 0CQT]
theorem isRightAdjoint_ι_iff_extensionProduct_leftOrthogonal_self_eq_top_and_isSaturated
    (B : ObjectProperty C) [B.IsStableUnderShift ℤ] :
    (B.ι.IsRightAdjoint ↔ B.leftOrthogonal.extensionProduct B = ⊤) ∧
      (B.leftOrthogonal.extensionProduct B = ⊤ →
        B.IsSaturated ∧ B.isoClosure = B.leftOrthogonal.rightOrthogonal) := by
  refine ⟨⟨fun _ ↦ ?_, fun htop ↦ ?_⟩, fun htop ↦ ?_⟩
  · -- (1) ⟹ (2): extend the unit at `X` to a distinguished triangle; its first object is in `ᗮB`
    -- because the unit is a universal arrow.
    have adj := Adjunction.ofIsRightAdjoint B.ι
    rw [eq_top_iff]
    intro X _
    obtain ⟨A, f, w, hT⟩ := distinguished_cocone_triangle₁ (adj.unit.app X)
    exact ⟨A, _, f, adj.unit.app X, w, hT, leftOrthogonal_obj₁_of_bijective B hT
      (fun W hW ↦ bijective_precomp_unit adj B.fullyFaithfulι X ⟨W, hW⟩),
      (B.ι.leftAdjoint.obj X).property⟩
  · -- (2) ⟹ (1): the third object of the triangle is the value of the left adjoint.
    choose A Z u v w hT hA hZ using exists_distTriang_of_extensionProduct_eq_top B htop
    refine isRightAdjoint_of_bijective_precomp B.ι (fun X ↦ ⟨Z X, hZ X⟩) v (fun X S ↦ ?_)
    exact (bijective_precomp_mor₂_of_leftOrthogonal B (hT X) (hA X) S.property).comp
      B.fullyFaithfulι.homEquiv.bijective
  · -- The final statement, both parts of which follow from `B.isoClosure = (ᗮB)ᗮ`.
    have hiso : B.isoClosure = B.leftOrthogonal.rightOrthogonal := by
      refine le_antisymm ((isoClosure_le_iff _ _).2 (le_rightOrthogonal_leftOrthogonal B))
        (fun X hX ↦ ?_)
      obtain ⟨A, B', u, v, w, hT, hA, hB'⟩ := exists_distTriang_of_extensionProduct_eq_top B htop X
      set T : Triangle C := Triangle.mk u v w
      have : IsIso T.mor₂ := (T.isZero₁_iff_isIso₂ hT).1
        (isZero_obj₁_of_rightOrthogonal_obj₂ B hT hA hX hB')
      exact ⟨B', hB', ⟨asIso T.mor₂⟩⟩
    have : B.isoClosure.IsStableUnderRetracts :=
      hiso ▸ (isStableUnderRetracts_rightOrthogonal_and_leftOrthogonal B.leftOrthogonal).1
    exact ⟨isSaturated_of_isStableUnderRetracts_isoClosure B, hiso⟩

/-! ### Extension products along a semiorthogonal pair -/

section Splitting

variable (P Q : ObjectProperty C)

/-- A biproduct of an object satisfying `P` and an object satisfying `Q` is an extension of the
first by the second, through the split triangle `Y ⟶ Y ⊞ Z ⟶ Z ⟶ Y⟦1⟧`. -/
private lemma extensionProduct_biprod {Y Z : C} (hY : P Y) (hZ : Q Z) :
    P.extensionProduct Q (Y ⊞ Z) :=
  ⟨Y, Z, biprod.inl, biprod.snd, 0, binaryBiproductTriangle_distinguished Y Z, hY, hZ⟩

/-- A distinguished triangle whose connecting map vanishes splits, so its middle object is an
extension of its third object by its first: for a split triangle the two orders of the extension
product agree. -/
private lemma extensionProduct_of_mor₃_eq_zero {T : Triangle C} (hT : T ∈ distTriang C)
    (hT₀ : T.mor₃ = 0) (h₁ : Q T.obj₁) (h₃ : P T.obj₃) : P.extensionProduct Q T.obj₂ := by
  obtain ⟨e, -, -⟩ := exists_iso_binaryBiproduct_of_distTriang T hT hT₀
  exact (P.extensionProduct Q).prop_of_iso (e.trans (biprod.braiding _ _)).symm
    (extensionProduct_biprod P Q h₃ h₁)

/-- If `Q` is contained in the right orthogonal of `P` and is stable under shifts, then an
extension of an object of `P` by an object of `Q` splits, so `extensionProduct Q P` is contained
in `extensionProduct P Q`. -/
private lemma extensionProduct_le_extensionProduct_of_le_rightOrthogonal
    [Q.IsStableUnderShift ℤ] (hQ : Q ≤ P.rightOrthogonal) :
    Q.extensionProduct P ≤ P.extensionProduct Q := by
  intro X ⟨Y, Z, f, g, h, hT, hY, hZ⟩
  exact extensionProduct_of_mor₃_eq_zero P Q hT (hQ _ (Q.le_shift 1 _ hY) h hZ) hY hZ

end Splitting

variable [IsTriangulated C]

/-- If extensions of an object of `B` by an object of `A` are also extensions of an object of `A`
by an object of `B`, then `A.extensionProduct B` is idempotent for the extension product: an
extension of one of its objects by another is again one of its objects. -/
private lemma extensionProduct_extensionProduct_self_le (A B : ObjectProperty C)
    [A.IsTriangulatedClosed₂] [B.IsTriangulatedClosed₂]
    (h : B.extensionProduct A ≤ A.extensionProduct B) :
    (A.extensionProduct B).extensionProduct (A.extensionProduct B) ≤ A.extensionProduct B :=
  calc (A.extensionProduct B).extensionProduct (A.extensionProduct B)
      = A.extensionProduct ((B.extensionProduct A).extensionProduct B) := by
        simp only [extensionProduct_assoc]
    _ ≤ A.extensionProduct ((A.extensionProduct B).extensionProduct B) :=
        monotone_extensionProduct_right _ (monotone_extensionProduct_left _ h)
    _ = (A.extensionProduct A).extensionProduct (B.extensionProduct B) := by
        simp only [extensionProduct_assoc]
    _ ≤ A.isoClosure.extensionProduct B.isoClosure :=
        (monotone_extensionProduct_left _
            (extensionProduct_le_of_isTriangulatedClosed₂' le_rfl le_rfl)).trans
          (monotone_extensionProduct_right _
            (extensionProduct_le_of_isTriangulatedClosed₂' le_rfl le_rfl))
    _ = A.extensionProduct B := by
        rw [extensionProduct_isoClosure_left, extensionProduct_isoClosure_right]

/-- Let `C` be a triangulated category, let `A` and `B` be triangulated subcategories of `C`
with `B` contained in the right orthogonal of `A`. Then the objects `X` of `C` that fit in a
distinguished triangle `A' ⟶ X ⟶ B' ⟶ A'⟦1⟧` with `A'` in `A` and `B'` in `B` form a
triangulated subcategory of `C`: they are stable under shifts, two out of three of them in a
distinguished triangle forces the third, and they are stable under direct sums. For
`B = A.rightOrthogonal` this is the property `P` of [Stacks, Tag 0CQR]. -/
@[stacks 0CQR]
theorem isTriangulated_extensionProduct_of_le_rightOrthogonal
    (A B : ObjectProperty C) [A.IsTriangulated] [B.IsTriangulated]
    (hB : B ≤ A.rightOrthogonal) :
    (A.extensionProduct B).IsTriangulated := by
  have : (A.extensionProduct B).ContainsZero := by
    obtain ⟨Z, hZ, hZA⟩ := A.exists_prop_of_containsZero
    exact ⟨Z, hZ, le_extensionProduct_left B _ hZA⟩
  have : (A.extensionProduct B).IsTriangulatedClosed₂ := .mk' fun T hT h₁ h₃ ↦
    extensionProduct_extensionProduct_self_le A B
      (extensionProduct_le_extensionProduct_of_le_rightOrthogonal A B hB) _
      ⟨_, _, T.mor₁, T.mor₂, T.mor₃, hT, h₁, h₃⟩
  exact { }

/-- Let `C` be a triangulated category and let `B` be a triangulated subcategory of `C`. Then
the objects `X` of `C` that fit in a distinguished triangle `A ⟶ X ⟶ B' ⟶ A⟦1⟧` with `A` in the
left orthogonal of `B` and `B'` in `B` form a triangulated subcategory of `C`: they are stable
under shifts, two out of three of them in a distinguished triangle forces the third, and they are
stable under direct sums. This is the property `P` of [Stacks, Tag 0H0N]. -/
@[stacks 0H0N]
theorem isTriangulated_extensionProduct_leftOrthogonal_self (B : ObjectProperty C)
    [B.IsTriangulated] :
    (B.leftOrthogonal.extensionProduct B).IsTriangulated :=
  isTriangulated_extensionProduct_of_le_rightOrthogonal _ _
    (le_rightOrthogonal_leftOrthogonal B)

/-! ### Semiorthogonal decompositions and Verdier quotients -/

omit [IsTriangulated C] in
/-- **The geometric step of [Stacks, Tag 0H0P].** If no nonzero morphism goes from `A` to `B` and
every object of `C` is an extension of an object of `B` by an object of `A`, then `A` is the whole
left orthogonal of `B`.

Given `X` in `ᗮB`, the triangle `A' ⟶ X ⟶ B' ⟶ A'⟦1⟧` provided by the extension property has
`X ⟶ B'` zero, so `𝟙 B'` factors through `B' ⟶ A'⟦1⟧`; the factoring morphism goes from `A'⟦1⟧`,
which lies in `A`, to `B'`, so it vanishes, `B'` is zero and `A' ⟶ X` is an isomorphism. -/
private lemma leftOrthogonal_le_of_extensionProduct (A B : ObjectProperty C)
    [A.IsClosedUnderIsomorphisms] [A.IsStableUnderShift ℤ] (hAB : A ≤ B.leftOrthogonal)
    (hext : A.extensionProduct B = ⊤) :
    B.leftOrthogonal ≤ A := by
  intro X hX
  obtain ⟨A', B', f, g, h, hT, hA', hB'⟩ : A.extensionProduct B X := by rw [hext]; trivial
  obtain ⟨φ, hφ⟩ := Triangle.yoneda_exact₃ _ hT (𝟙 B') (by simpa using hX g hB')
  have hφ0 : φ = 0 := hAB _ (A.le_shift (1 : ℤ) _ hA') φ hB'
  have hz : IsZero B' := by
    rw [IsZero.iff_id_eq_zero, hφ, hφ0, comp_zero]
  have : IsIso f := (Triangle.isZero₃_iff_isIso₁ _ hT).1 hz
  exact A.prop_of_iso (asIso f) hA'

omit [IsTriangulated C] in
/-- Under condition (3) of [Stacks, Tag 0H0P], each of `A`, `B` is the orthogonal of the other:
`A = ᗮB` is `leftOrthogonal_le_of_extensionProduct`, and `B = Aᗮ` then follows from the second
half of [Stacks, Tag 0CQT], `B` being strictly full. -/
private lemma eq_of_extensionProduct (A B : ObjectProperty C) [A.IsClosedUnderIsomorphisms]
    [B.IsClosedUnderIsomorphisms] [A.IsStableUnderShift ℤ] [B.IsStableUnderShift ℤ]
    (hAB : A ≤ B.leftOrthogonal) (hext : A.extensionProduct B = ⊤) :
    A = B.leftOrthogonal ∧ B = A.rightOrthogonal := by
  have hA : A = B.leftOrthogonal :=
    le_antisymm hAB (leftOrthogonal_le_of_extensionProduct A B hAB hext)
  refine ⟨hA, ?_⟩
  have hext' : B.leftOrthogonal.extensionProduct B = ⊤ := by rw [← hA]; exact hext
  have hiso :=
    ((isRightAdjoint_ι_iff_extensionProduct_leftOrthogonal_self_eq_top_and_isSaturated B).2
      hext').2
  rw [B.isoClosure_eq_self] at hiso
  rw [hA]
  exact hiso

omit [IsTriangulated C] in
/-- **The three conditions of [Stacks, Tag 0H0P] are equivalent.** -/
private lemma tfae_admissible_aux (A B : ObjectProperty C) [A.IsClosedUnderIsomorphisms]
    [B.IsClosedUnderIsomorphisms] [A.IsStableUnderShift ℤ] [B.IsStableUnderShift ℤ] :
    [A.IsRightAdmissible ∧ B = A.rightOrthogonal,
      B.IsLeftAdmissible ∧ A = B.leftOrthogonal,
      A ≤ B.leftOrthogonal ∧ A.extensionProduct B = ⊤].TFAE := by
  tfae_have 1 → 3 := by
    rintro ⟨hadm, hB⟩
    have := hadm
    refine ⟨?_, ?_⟩
    · rw [hB]
      exact le_leftOrthogonal_rightOrthogonal A
    · rw [hB]
      exact (isLeftAdjoint_ι_iff_extensionProduct_rightOrthogonal_eq_top_and_isSaturated A).1.1
        inferInstance
  tfae_have 2 → 3 := by
    rintro ⟨hadm, hA⟩
    have := hadm
    refine ⟨le_of_eq hA, ?_⟩
    rw [hA]
    exact (isRightAdjoint_ι_iff_extensionProduct_leftOrthogonal_self_eq_top_and_isSaturated B).1.1
      inferInstance
  tfae_have 3 → 1 := by
    rintro ⟨hAB, hext⟩
    obtain ⟨hA, hB⟩ := eq_of_extensionProduct A B hAB hext
    have : A.IsTriangulated := by rw [hA]; infer_instance
    have : A.ι.IsLeftAdjoint :=
      (isLeftAdjoint_ι_iff_extensionProduct_rightOrthogonal_eq_top_and_isSaturated A).1.2
        (by rw [← hB]; exact hext)
    exact ⟨⟨⟩, hB⟩
  tfae_have 3 → 2 := by
    rintro ⟨hAB, hext⟩
    obtain ⟨hA, hB⟩ := eq_of_extensionProduct A B hAB hext
    have : B.IsTriangulated := by rw [hB]; infer_instance
    have : B.ι.IsRightAdjoint :=
      (isRightAdjoint_ι_iff_extensionProduct_leftOrthogonal_self_eq_top_and_isSaturated B).1.2
        (by rw [← hA]; exact hext)
    exact ⟨⟨⟩, hA⟩
  tfae_finish

omit [IsTriangulated C] in
/-- The composite of `A.ι` with a localization of `C` at `B.trW` is essentially surjective: an
object of the quotient is `L X`, and the triangle `A' ⟶ X ⟶ B' ⟶ A'⟦1⟧` makes `A' ⟶ X` a morphism
of `B.trW`, which `L` inverts. -/
private lemma essSurj_ι_comp (A B : ObjectProperty C) (hext : A.extensionProduct B = ⊤)
    {Q : Type w} [Category.{w'} Q] (L : C ⥤ Q) [L.IsLocalization B.trW] :
    (A.ι ⋙ L).EssSurj where
  mem_essImage Z := by
    have := Localization.essSurj L B.trW
    obtain ⟨A', B', f, g, h, hT, hA', hB'⟩ :
        A.extensionProduct B (L.objPreimage Z) := by rw [hext]; trivial
    have : IsIso (L.map f) := Localization.inverts L B.trW f ⟨B', g, h, hT, hB'⟩
    exact ⟨⟨A', hA'⟩, ⟨asIso (L.map f) ≪≫ L.objObjPreimageIso Z⟩⟩

/-- `L` is bijective on morphisms out of an object of `A`: those objects lie in `ᗮB`. Since the
morphisms of a full subcategory are those of `C`, this is bijectivity of the map on morphisms
of `A.ι ⋙ L`. -/
private lemma map_bijective_of_le (A B : ObjectProperty C) [B.IsTriangulated]
    (hAB : A ≤ B.leftOrthogonal)
    {Q : Type w} [Category.{w'} Q] (L : C ⥤ Q) [L.IsLocalization B.trW]
    (X : A.FullSubcategory) (Y : C) :
    Function.Bijective (L.map : (X.obj ⟶ Y) → _) :=
  leftOrthogonal.map_bijective_of_isTriangulated (hAB _ X.property) L Y

/-- **`A` is equivalent to the Verdier quotient of `C` by `B`.** -/
@[sga "4½ Etat_0 4.2.3" "(b), special case"]
private lemma isEquivalence_ι_comp (A B : ObjectProperty C) [B.IsTriangulated]
    (hAB : A ≤ B.leftOrthogonal) (hext : A.extensionProduct B = ⊤)
    {Q : Type w} [Category.{w'} Q] (L : C ⥤ Q) [L.IsLocalization B.trW] :
    (A.ι ⋙ L).IsEquivalence := by
  exact isEquivalence_ι_comp_of_map_bijective L
    (fun X Y ↦ map_bijective_of_le A B hAB L X Y.obj) (essSurj_ι_comp A B hext L)

omit [IsTriangulated C] in
/-- A right adjoint of `A.ι` inverts `B.trW`. By Yoneda it suffices that composition with `R f` be
bijective on morphisms out of an object of `A`, and the adjunction turns that into composition
with `f`, which is bijective because the objects of `A` are `B.trW`-colocal. -/
private lemma isInvertedBy_of_adjunction (A B : ObjectProperty C) [B.IsTriangulated]
    (hAB : A ≤ B.leftOrthogonal) {R : C ⥤ A.FullSubcategory} (adj : A.ι ⊣ R) :
    B.trW.IsInvertedBy R := by
  intro X Y f hf
  rw [isIso_iff_yoneda_map_bijective]
  intro T
  have hT : B.trW.isColocal T.obj := by
    rw [isColocal_trW]
    exact hAB _ T.property
  exact bijective_postcomp_of_bijective (adj.homEquiv T X) (adj.homEquiv T Y)
    (fun g ↦ (adj.homEquiv_naturality_right g f).symm) (hT f hf)

omit [IsTriangulated C] in
/-- **A right adjoint of `A.ι` factors through the Verdier quotient by `B`.** -/
private lemma exists_adjunction_ι (A B : ObjectProperty C) [B.IsTriangulated]
    (hAB : A ≤ B.leftOrthogonal) [A.ι.IsLeftAdjoint]
    {Q : Type w} [Category.{w'} Q] (L : C ⥤ Q) [L.IsLocalization B.trW] :
    ∃ G : Q ⥤ A.FullSubcategory, Nonempty (A.ι ⊣ L ⋙ G) := by
  have adj := Adjunction.ofIsLeftAdjoint A.ι
  have hR := isInvertedBy_of_adjunction A B hAB adj
  exact ⟨Localization.lift _ hR L,
    ⟨Adjunction.ofNatIsoRight adj (Localization.fac _ hR L).symm⟩⟩

omit [IsTriangulated C] in
/-- Dual to `essSurj_ι_comp`: the cone of `X ⟶ B'` is `A'⟦1⟧`, which lies in `A`, so `X ⟶ B'` is a
morphism of `A.trW`. -/
private lemma essSurj_ι_comp' (A B : ObjectProperty C) [A.IsStableUnderShift ℤ]
    (hext : A.extensionProduct B = ⊤)
    {Q : Type w} [Category.{w'} Q] (L : C ⥤ Q) [L.IsLocalization A.trW] :
    (B.ι ⋙ L).EssSurj where
  mem_essImage Z := by
    have := Localization.essSurj L A.trW
    obtain ⟨A', B', f, g, h, hT, hA', hB'⟩ :
        A.extensionProduct B (L.objPreimage Z) := by rw [hext]; trivial
    have : IsIso (L.map g) := Localization.inverts L A.trW g
      ⟨A'⟦(1 : ℤ)⟧, h, -(f⟦(1 : ℤ)⟧'), rot_of_distTriang _ hT, A.le_shift (1 : ℤ) _ hA'⟩
    exact ⟨⟨B', hB'⟩, ⟨(asIso (L.map g)).symm ≪≫ L.objObjPreimageIso Z⟩⟩

/-- Dual to `map_bijective_of_le`. -/
private lemma map_bijective_of_le' (A B : ObjectProperty C) [A.IsTriangulated]
    (hBA : B ≤ A.rightOrthogonal)
    {Q : Type w} [Category.{w'} Q] (L : C ⥤ Q) [L.IsLocalization A.trW]
    (X : C) (Y : B.FullSubcategory) :
    Function.Bijective (L.map : (X ⟶ Y.obj) → _) :=
  rightOrthogonal.map_bijective_of_isTriangulated (hBA _ Y.property) L X

/-- **`B` is equivalent to the Verdier quotient of `C` by `A`.** -/
@[sga "4½ Etat_0 4.2.3" "(b), special case"]
private lemma isEquivalence_ι_comp' (A B : ObjectProperty C) [A.IsTriangulated]
    (hBA : B ≤ A.rightOrthogonal) (hext : A.extensionProduct B = ⊤)
    {Q : Type w} [Category.{w'} Q] (L : C ⥤ Q) [L.IsLocalization A.trW] :
    (B.ι ⋙ L).IsEquivalence := by
  exact isEquivalence_ι_comp_of_map_bijective L
    (fun X Y ↦ map_bijective_of_le' A B hBA L X.obj Y) (essSurj_ι_comp' A B hext L)

omit [IsTriangulated C] in
/-- Dual to `isInvertedBy_of_adjunction`: a left adjoint of `B.ι` inverts `A.trW`, the objects
of `B` being `A.trW`-local. -/
private lemma isInvertedBy_of_adjunction' (A B : ObjectProperty C) [A.IsTriangulated]
    (hBA : B ≤ A.rightOrthogonal) {F : C ⥤ B.FullSubcategory} (adj : F ⊣ B.ι) :
    A.trW.IsInvertedBy F := by
  intro X Y f hf
  rw [isIso_iff_coyoneda_map_bijective]
  intro T
  have hT : A.trW.isLocal T.obj := by
    rw [isLocal_trW]
    exact hBA _ T.property
  have key : (fun (x : F.obj Y ⟶ T) => F.map f ≫ x) =
      (adj.homEquiv X T).symm ∘ (fun (y : Y ⟶ B.ι.obj T) => f ≫ y) ∘ (adj.homEquiv Y T) := by
    funext x
    simp only [Function.comp_apply, ← Adjunction.homEquiv_naturality_left,
      Equiv.symm_apply_apply]
  rw [key]
  exact (adj.homEquiv X T).symm.bijective.comp ((hT f hf).comp (adj.homEquiv Y T).bijective)

omit [IsTriangulated C] in
/-- **A left adjoint of `B.ι` factors through the Verdier quotient by `A`.** -/
private lemma exists_adjunction_ι' (A B : ObjectProperty C) [A.IsTriangulated]
    (hBA : B ≤ A.rightOrthogonal) [B.ι.IsRightAdjoint]
    {Q : Type w} [Category.{w'} Q] (L : C ⥤ Q) [L.IsLocalization A.trW] :
    ∃ G : Q ⥤ B.FullSubcategory, Nonempty (L ⋙ G ⊣ B.ι) := by
  have adj := Adjunction.ofIsRightAdjoint B.ι
  have hF := isInvertedBy_of_adjunction' A B hBA adj
  exact ⟨Localization.lift _ hF L,
    ⟨Adjunction.ofNatIsoLeft adj (Localization.fac _ hF L).symm⟩⟩

/-- Let `C` be a triangulated category and let `A B : ObjectProperty C` be strictly full and
invariant under all shifts. Then: `A` is right admissible with `B = Aᗮ` if and only if `B` is left
admissible with `A = ᗮB` if and only if `Hom(A', B') = 0` for `A'` in `A` and `B'` in `B` and every
object `X` of `C` fits in a distinguished triangle `A' ⟶ X ⟶ B' ⟶ A'⟦1⟧` with `A' ∈ A`, `B' ∈ B`.
If this holds, then for every Verdier quotient `L : C ⥤ Q` of `C` by `B`, i.e. every localization
of `C` at `B.trW`, the composite `A.ι ⋙ L : A ⥤ Q` is an equivalence and a right adjoint of the
inclusion `A.ι` is `L ⋙ G` for some `G : Q ⥤ A`, necessarily a quasi-inverse of `A.ι ⋙ L`; and
dually for the Verdier quotient of `C` by `A`, the inclusion `B.ι` and its left adjoint. -/
@[stacks 0H0P, sga "4½ Etat_0 2.6.6"]
theorem tfae_isRightAdmissible_isLeftAdmissible_extensionProduct_and_isEquivalence_ι_comp
    (A B : ObjectProperty C) [A.IsClosedUnderIsomorphisms] [B.IsClosedUnderIsomorphisms]
    [A.IsStableUnderShift ℤ] [B.IsStableUnderShift ℤ] :
    [A.IsRightAdmissible ∧ B = A.rightOrthogonal,
      B.IsLeftAdmissible ∧ A = B.leftOrthogonal,
      A ≤ B.leftOrthogonal ∧ A.extensionProduct B = ⊤].TFAE ∧
    (A ≤ B.leftOrthogonal → A.extensionProduct B = ⊤ →
      (∀ {Q : Type w} [Category.{w'} Q] (L : C ⥤ Q) [L.IsLocalization B.trW],
          (A.ι ⋙ L).IsEquivalence ∧
            ∃ G : Q ⥤ A.FullSubcategory, Nonempty (A.ι ⊣ L ⋙ G)) ∧
      (∀ {Q : Type w} [Category.{w'} Q] (L : C ⥤ Q) [L.IsLocalization A.trW],
          (B.ι ⋙ L).IsEquivalence ∧
            ∃ G : Q ⥤ B.FullSubcategory, Nonempty (L ⋙ G ⊣ B.ι))) := by
  refine ⟨tfae_admissible_aux A B, fun hAB hext => ?_⟩
  obtain ⟨hA, hB⟩ := eq_of_extensionProduct A B hAB hext
  have : A.IsTriangulated := by rw [hA]; infer_instance
  have : B.IsTriangulated := by rw [hB]; infer_instance
  have : A.ι.IsLeftAdjoint :=
    (isLeftAdjoint_ι_iff_extensionProduct_rightOrthogonal_eq_top_and_isSaturated A).1.2
      (by rw [← hB]; exact hext)
  have : B.ι.IsRightAdjoint :=
    (isRightAdjoint_ι_iff_extensionProduct_leftOrthogonal_self_eq_top_and_isSaturated B).1.2
      (by rw [← hA]; exact hext)
  have hBA := le_rightOrthogonal_of_le_leftOrthogonal hAB
  constructor
  · intro Q _ L _
    exact ⟨isEquivalence_ι_comp A B hAB hext L, exists_adjunction_ι A B hAB L⟩
  · intro Q _ L _
    exact ⟨isEquivalence_ι_comp' A B hBA hext L, exists_adjunction_ι' A B hBA L⟩

end Admissible

end CategoryTheory.ObjectProperty

end

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-
# Problem Description

Stacks Tag 0CQQ / Lemma 13.40.2.

Let `D` be a triangulated category (in particular additive, so each Hom-set is an
abelian group), with shift (translation) auto-equivalence `[1]` and `n`-fold shift
`[n]` for `n : ℤ`.

A full subcategory `A ⊆ D` is *invariant under all shifts* if for every object
`A` of `A` and every integer `n`, the shifted object `A[n]` is (isomorphic to an
object) in `A`.

The *right orthogonal* `Aᗮ` of `A` is the full subcategory of `D` consisting of
those objects `Z` such that `Hom_D(A, Z) = 0` for all objects `A` of `A`.

Statement: Let `A ⊆ D` be a full subcategory invariant under all shifts.
Consider a distinguished triangle
  `X --f--> Y --g--> Z --h--> X[1]`.
Then the following are equivalent:
1. `Z` is in `Aᗮ`, i.e. `Hom_D(A, Z) = 0` for all objects `A` of `A`.
2. For every object `A` of `A`, the map
   `f_* : Hom_D(A, X) → Hom_D(A, Y)`, `g ↦ g ≫ f`,
   induced by post-composition with `f`, is an isomorphism of abelian groups.
-/

-- Background and context (as comments)
-- We model the ambient triangulated category `D` as a Mathlib `Pretriangulated`
-- category `C` that is preadditive, has a zero object, and additive shift functors;
-- this is exactly the data of a triangulated category in Mathlib. Hom-sets are then
-- abelian groups via `Preadditive`.
--
-- A full subcategory `A ⊆ D` is represented by its predicate on objects
-- `P : C → Prop` ("A is the full subcategory on objects satisfying `P`"). Being a
-- *full* subcategory means morphisms are inherited, so a predicate on objects
-- carries all the relevant data.
--
-- IMPORTANT (addressing prior feedback): "invariant under all shifts" must be read
-- up to isomorphism. The shifted object `A[n]` need not literally satisfy the
-- predicate `P`; it only needs to be *isomorphic* to some object satisfying `P`.
-- We therefore define invariance up to isomorphism. This correctly captures the
-- informal definition even for non-replete full subcategories.
--
-- "Hom(A, Z) = 0 as an abelian group" is expressed as: every morphism `A ⟶ Z`
-- is the zero morphism.
--
-- The induced map `f_* : Hom(A, X) → Hom(A, Y)` is post-composition `g ↦ g ≫ f`
-- (recall Mathlib's `≫` is left-to-right composition). "Isomorphism of abelian
-- groups" is expressed as `Function.Bijective`, which for an additive map is
-- equivalent to being a group isomorphism.

open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Limits

namespace Stacks.Triangulated.RightOrthogonal

variable {C : Type*} [Category C] [HasShift C ℤ] [Preadditive C] [HasZeroObject C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

-- Main Definition(s)

/-- Definition 1: a full subcategory of `C`, described by its predicate `P` on
objects, is *invariant under all shifts* if for every `n : ℤ` and every object `A`
with `P A`, the shifted object `A⟦n⟧` is *isomorphic to* some object satisfying
`P`. Invariance is taken up to isomorphism, matching the informal statement and
covering non-replete full subcategories. -/
def InvariantUnderAllShifts (P : C → Prop) : Prop :=
  ∀ (n : ℤ) (A : C), P A →
    ∃ B : C, P B ∧ Nonempty (((shiftFunctor C n).obj A) ≅ B)

/-- Definition 2: an object `Z` is in the right orthogonal `Aᗮ` of the full
subcategory described by `P` if `Hom(A, Z) = 0` for every object `A` with `P A`,
i.e. every morphism `A ⟶ Z` is zero. -/
@[sga "4½ Etat_0 2.6.2"]
def InRightOrthogonal (P : C → Prop) (Z : C) : Prop :=
  ∀ (A : C), P A → ∀ (g : A ⟶ Z), g = 0

-- Helper lemmas
--
-- The proof of the main lemma factors through four helper_0cqq facts. We record them as
-- named sub-lemmas; together with the main `iff` proof they form the decomposition
-- of Stacks Tag 0CQQ. Each helper_0cqq has a one-paragraph informal justification in its
-- doc-comment; the formal proofs are complete (verified in environment `stacks`).

/-- **Helper 1 (`hom_shift_eq_zero`).**
If `Z` lies in the right orthogonal of the shift-invariant subcategory `P` and
`P A` holds, then every morphism out of the shifted object `A⟦n⟧` into `Z` is zero.

*Argument.* By shift-invariance there is `B` with `P B` and an iso `e : A⟦n⟧ ≅ B`.
For any `u : A⟦n⟧ ⟶ Z`, the composite `e.inv ≫ u : B ⟶ Z` is zero because `Z` is
right-orthogonal and `P B`. Then `u = e.hom ≫ e.inv ≫ u = e.hom ≫ 0 = 0`. -/
private lemma hom_shift_eq_zero (P : C → Prop) (hP : InvariantUnderAllShifts P)
    {Z : C} (hZ : InRightOrthogonal P Z) (n : ℤ) {A : C} (hA : P A)
    (u : (shiftFunctor C n).obj A ⟶ Z) : u = 0 := by
  obtain ⟨B, hB, ⟨e⟩⟩ := hP n A hA
  have hzero : e.inv ≫ u = 0 := hZ B hB (e.inv ≫ u)
  calc u = e.hom ≫ e.inv ≫ u := by
            rw [← Category.assoc, e.hom_inv_id, Category.id_comp]
    _ = e.hom ≫ 0 := by rw [hzero]
    _ = 0 := by rw [comp_zero]

/-- **Helper 2 (`hom_to_shift_eq_zero`).**
Consequence of Helper 1 via the shift adjunction: when `P A` and `Z` is in the
right orthogonal of the shift-invariant `P`, every morphism `A ⟶ Z⟦-n⟧` is zero.

*Argument.* The shift auto-equivalence gives an adjunction with hom-equivalence
`E : (A⟦n⟧ ⟶ Z) ≃ (A ⟶ Z⟦-n⟧)`. Given `w : A ⟶ Z⟦-n⟧`, the morphism `E.symm w :
A⟦n⟧ ⟶ Z` is zero by Helper 1, hence `w = E (E.symm w) = E 0 = 0`, using that the
hom-equivalence sends `0` to `0` (it is additive). -/
@[sga "4½ Etat_0 2.6.2" "partial"]
private lemma hom_to_shift_eq_zero (P : C → Prop) (hP : InvariantUnderAllShifts P)
    {Z : C} (hZ : InRightOrthogonal P Z) (n : ℤ) {A : C} (hA : P A)
    (w : A ⟶ (shiftFunctor C (-n)).obj Z) : w = 0 := by
  set E := (shiftEquiv C n).toAdjunction.homEquiv A Z with hE
  have h1 : E.symm w = 0 := hom_shift_eq_zero P hP hZ n hA (E.symm w)
  have h2 : w = E (E.symm w) := (E.apply_symm_apply w).symm
  rw [h2, h1]
  simp [hE, Adjunction.homEquiv_apply]

/-- **Helper 3 (`bijective_postcomp_of_iso`).**
Bijectivity of post-composition with `f` is transported along an isomorphism `e`
of the source object: if `· ≫ f` is bijective on `Hom(A', X)` and `A ≅ A'`, then
`· ≫ f` is bijective on `Hom(A, X)`. -/
private lemma bijective_postcomp_of_iso {A A' X Y : C} (f : X ⟶ Y) (e : A ≅ A')
    (h : Function.Bijective (fun g : A' ⟶ X => g ≫ f)) :
    Function.Bijective (fun g : A ⟶ X => g ≫ f) :=
  ObjectProperty.bijective_postcomp_of_bijective (e.symm.homCongr (Iso.refl X))
    (e.symm.homCongr (Iso.refl Y)) (fun g ↦ by simp [Iso.homCongr]) h

-- Main Statement(s)

/-- Stacks Tag 0CQQ / Lemma 13.40.2.

Let `A ⊆ D` (described by `P`) be a full subcategory invariant under all shifts
(up to isomorphism), and let `X --f--> Y --g--> Z --h--> X[1]` be a distinguished
triangle. Then `Z` is in the right orthogonal `Aᗮ` if and only if, for every
object `A` of `A`, the map `f_* : Hom(A, X) → Hom(A, Y)`, `g ↦ g ≫ f`, is an
isomorphism of abelian groups (here expressed as a bijection).

Proof outline (as in the source), applying the homological functor `Hom(A,-)`:
* `(1) ⇒ (2)`: injectivity of `f_*` uses the inverse-rotated triangle
  `Z⟦-1⟧ → X → Y` and `coyoneda_exact₂`: a kernel element factors through
  `Z⟦-1⟧`, which vanishes by `hom_to_shift_eq_zero`; surjectivity uses
  `coyoneda_exact₂` on `T` since `u ≫ g = 0` for any `u : A ⟶ Y` (as `Z ∈ Aᗮ`).
* `(2) ⇒ (1)`: for `u : A ⟶ Z`, first `u ≫ h = 0` by injectivity of `· ≫ f⟦1⟧`
  (Helper 3 and `bijective_postcomp_shift` transport bijectivity to `Hom(A, X⟦1⟧)`) together with
  `comp_distTriang_mor_zero₂₃` on the rotated triangle; then `coyoneda_exact₂` on
  the rotated triangle factors `u = v ≫ g`, surjectivity of `f_*` gives `v = w ≫ f`,
  and `f ≫ g = 0` yields `u = w ≫ (f ≫ g) = 0`. -/
@[stacks 0CQQ]
theorem inRightOrthogonal_iff_postcomp_bijective
    (P : C → Prop) (hP : InvariantUnderAllShifts P)
    (T : Triangle C) (hT : T ∈ distinguishedTriangles) :
    InRightOrthogonal P T.obj₃ ↔
      ∀ (A : C), P A → Function.Bijective (fun g : A ⟶ T.obj₁ => g ≫ T.mor₁) := by
  constructor
  · -- (1) ⟹ (2)
    intro hZ A hA
    refine ⟨?_, ?_⟩
    · -- injective
      intro a b hab
      -- reduce to kernel: (a - b) ≫ f = 0
      have hsub : (a - b) ≫ T.mor₁ = 0 := by
        rw [Preadditive.sub_comp]
        simp only at hab
        rw [hab, sub_self]
      -- use the inverse-rotated distinguished triangle  Z⟦-1⟧ → X → Y
      have hT' : T.invRotate ∈ distinguishedTriangles := inv_rot_of_distTriang T hT
      obtain ⟨w, hw⟩ := T.invRotate.coyoneda_exact₂ hT' (X := A) (a - b) (by
        simpa using hsub)
      -- w : A ⟶ Z⟦-1⟧ vanishes by Helper 2
      have hwz : w = 0 :=
        hom_to_shift_eq_zero P hP hZ 1 hA w
      have : a - b = 0 := by rw [hw, hwz, zero_comp]
      exact sub_eq_zero.mp this
    · -- surjective
      intro u
      -- u : A ⟶ Y;  u ≫ g : A ⟶ Z is zero, so u factors through f
      have hug : u ≫ T.mor₂ = 0 := hZ A hA (u ≫ T.mor₂)
      obtain ⟨v, hv⟩ := T.coyoneda_exact₂ hT (X := A) u hug
      exact ⟨v, hv.symm⟩
  · -- (2) ⟹ (1)
    intro hbij A hA u
    -- We show every `u : A ⟶ Z` is zero.
    -- shift invariance: A⟦-1⟧ ≅ B with P B
    obtain ⟨B, hB, ⟨e⟩⟩ := hP (-1) A hA
    have hbB := hbij B hB
    -- transport along e : A⟦-1⟧ ≅ B  to Hom(A⟦-1⟧, X)  (Helper 3)
    have hbAshift :
        Function.Bijective (fun g : (shiftFunctor C (-1 : ℤ)).obj A ⟶ T.obj₁ => g ≫ T.mor₁) :=
      bijective_postcomp_of_iso T.mor₁ e hbB
    -- bridge to `· ≫ f⟦1⟧` on Hom(A, X⟦1⟧)
    have hbridge := ObjectProperty.bijective_postcomp_shift T.mor₁ 1 hbAshift
    -- u ≫ h = 0, via comp_distTriang_mor_zero₂₃ on the rotated triangle
    have hT'' : T.rotate ∈ distinguishedTriangles := rot_of_distTriang T hT
    have hzero23 : T.rotate.mor₂ ≫ T.rotate.mor₃ = 0 :=
      comp_distTriang_mor_zero₂₃ T.rotate hT''
    have huh : (u ≫ T.mor₃) ≫ (shiftFunctor C (1 : ℤ)).map T.mor₁ = 0 := by
      have : u ≫ (T.rotate.mor₂ ≫ T.rotate.mor₃) = 0 := by rw [hzero23, comp_zero]
      have hr3 : T.rotate.mor₃ = -(shiftFunctor C 1).map T.mor₁ := by
        simp [Triangle.rotate]
      rw [show T.rotate.mor₂ = T.mor₃ from rfl, hr3] at this
      rw [Preadditive.comp_neg, Preadditive.comp_neg, ← Category.assoc] at this
      simpa [Category.assoc] using neg_eq_zero.mp this
    -- injectivity of `· ≫ f⟦1⟧` on Hom(A, X⟦1⟧) gives u ≫ h = 0
    have huh0 : u ≫ T.mor₃ = 0 := hbridge.1 (by simpa using huh)
    -- factor u through g using the rotated triangle Y → Z → X⟦1⟧
    obtain ⟨v, hv⟩ := T.rotate.coyoneda_exact₂ hT'' (X := A) u (by
      simpa [show T.rotate.mor₂ = T.mor₃ from rfl] using huh0)
    -- f_* surjective on A: v = w ≫ f
    obtain ⟨w, hw⟩ := (hbij A hA).2 v
    -- u = (w ≫ f) ≫ g = w ≫ (f ≫ g) = 0
    have hfg : T.mor₁ ≫ T.mor₂ = 0 := comp_distTriang_mor_zero₁₂ T hT
    rw [hv, show T.rotate.mor₁ = T.mor₂ from rfl, ← hw]
    simp only
    rw [Category.assoc, hfg, comp_zero]

end Stacks.Triangulated.RightOrthogonal

end

end

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

Stacks Tag 0H0M (Lemma 13.40.3).

Let `D` be a triangulated category. Let `B ⊂ D` be a full subcategory invariant under all
shifts. Consider a distinguished triangle

  X --f--> Y --g--> Z --h--> X[1]

of `D`. Then the following are equivalent.

1. `X` is in the left orthogonal `ᗮB`, i.e. `Hom_D(X, B) = 0` for all objects `B` of `B`.
2. For all objects `B` of `B`, the precomposition map
     g* : Hom_D(Z, B) → Hom_D(Y, B),   φ ↦ φ ∘ g
   is bijective.

# Interpretation

The phrase "Hom(Y, B) = Hom(Z, B)" in the Stacks statement is not a literal equality of two
hom-sets (which live over different objects). Following the dual lemma (Stacks Tag 0CQQ),
the intended meaning is that the canonical map between the two hom-groups — the one induced by
the triangle morphism `g : Y → Z` via precomposition — is an isomorphism of abelian groups
(here expressed as a bijection of the underlying hom-sets, equivalently an isomorphism of the
abelian hom-groups).

# Dependencies (available, cite rather than reprove)

- Stacks 0146: `CategoryTheory.Pretriangulated.comp_distTriang_mor_zero₁₂`.
- Stacks 0148: `CategoryTheory.Functor.homologySequenceComposableArrows₅_exact`.
- Stacks 0149: `CategoryTheory.Pretriangulated.instIsHomological...Coyoneda` (the instance that
  `Hom(-, B)` is homological on `Dᵒᵖ`).
-/

open CategoryTheory CategoryTheory.Pretriangulated Limits

namespace Stacks.Triangulated.AdmissibleSubcategories

variable {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]

-- Main Definition(s)

/-- **Definition 1 (Left orthogonal).** Given a full subcategory `B ⊂ D` (identified with a
predicate on objects), an object `X` lies in the left orthogonal `ᗮB` of `B` iff for every
object `Z` with `Z ∈ B`, every morphism `X ⟶ Z` is the zero morphism, i.e. the hom-group
`Hom_D(X, Z)` is the zero group. -/
@[sga "4½ Etat_0 2.5.4", sga "4½ Etat_0 2.6.2"]
def IsLeftOrthogonal (B : D → Prop) (X : D) : Prop :=
  ∀ (Z : D), B Z → ∀ (φ : X ⟶ Z), φ = 0

/-- **Definition 2 (Invariant under all shifts).** A full subcategory `B ⊂ D` (a predicate on
objects) is invariant under all shifts if for every object `Z` with `Z ∈ B` and every integer
`n`, the shifted object `Z⟦n⟧` also lies in `B`. -/
def ShiftInvariant (B : D → Prop) : Prop :=
  ∀ (Z : D), B Z → ∀ (n : ℤ), B ((shiftFunctor D n).obj Z)

/-- **Definition 3 (The induced map on hom-sets).** Given a triangle
`X --f--> Y --g--> Z --h--> X[1]` and an object `B`, the morphism `g : Y ⟶ Z` induces, by
precomposition, the map `g* : Hom_D(Z, B) → Hom_D(Y, B)`, `φ ↦ φ ∘ g = g ≫ φ`. -/
def precompMap (T : Triangle D) (B : D) : (T.obj₃ ⟶ B) → (T.obj₂ ⟶ B) :=
  fun φ => T.mor₂ ≫ φ

-- Helper lemmas

omit [HasZeroObject D] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D] in
/-- **Helper (shift orthogonality).** Under left orthogonality of `X` and shift invariance of
`B`, every morphism from a shift `X⟦n⟧` into an object `b ∈ B` is zero.

Mathematical content: `Hom(X⟦n⟧, b) ≅ Hom(X, b⟦-n⟧)` by the shift adjunction (the shift
functors form an equivalence `shiftEquiv D n`), and `b⟦-n⟧ ∈ B` by shift invariance, so the
right-hand group is `0` by left orthogonality; transporting back, the morphism is `0`. -/
@[sga "4½ Etat_0 2.6.2" "partial"]
theorem orthShift (B : D → Prop) (hB : ShiftInvariant B) (X : D)
    (hX : IsLeftOrthogonal B X) (n : ℤ) (b : D) (hb : B b)
    (β : (shiftFunctor D n).obj X ⟶ b) : β = 0 := by
  have hadj := (shiftEquiv D n).toAdjunction
  have heq := hadj.homEquiv X b
  have hbinv : B ((shiftEquiv D n).inverse.obj b) := by
    change B ((shiftFunctor D (-n)).obj b)
    exact hB b hb (-n)
  have h1 : heq β = 0 := hX _ hbinv _
  have h0 : heq (0 : (shiftEquiv D n).functor.obj X ⟶ b) = 0 := hX _ hbinv _
  exact heq.injective (h1.trans h0.symm)

omit [HasZeroObject D] [Pretriangulated D] in
/-- **Helper (the inverse-rotation gap).** In the backward direction of the main theorem we
must show that the first morphism `T.invRotate.mor₁ : Z⟦-1⟧ ⟶ X` of the inverse-rotated
triangle, postcomposed with `α : X ⟶ b`, vanishes — given that `h* = 0`, i.e. every
postcomposition `T.mor₃ ≫ β` (for `β : X⟦1⟧ ⟶ b'`, `b' ∈ B`) is zero.

Mathematical content (rigorous argument):

By definition of `invRotate` in Mathlib,
`T.invRotate.mor₁ = -(T.mor₃)⟦-1⟧' ≫ e.hom.app X`,
where `e := shiftFunctorCompIsoId D 1 (-1)` is the canonical isomorphism
`shiftFunctor 1 ⋙ shiftFunctor (-1) ≅ 𝟭`. (Verified by `rfl` in the target environment.)
Hence
`T.invRotate.mor₁ ≫ α = -( (T.mor₃)⟦-1⟧' ≫ (e.hom.app X ≫ α) )`,
so it suffices to show `(T.mor₃)⟦-1⟧' ≫ (e.hom.app X ≫ α) = 0` (`Preadditive.neg_comp`,
`neg_eq_zero`).

The morphism `(T.mor₃)⟦-1⟧' ≫ (e.hom.app X ≫ α) : Z⟦-1⟧ ⟶ b` is the `(-1)`-shift transport
of a morphism out of `Z`. Concretely, the shift functor `shiftFunctor D 1` is faithful (it is
an equivalence), so it suffices to prove the image under `(·)⟦1⟧'` is `0`. Applying `(·)⟦1⟧'`
and using functoriality, naturality of the unit/counit isomorphisms
(`shiftFunctorCompIsoId D (-1) 1` and `shiftFunctorCompIsoId D 1 (-1)`), one identifies
`((T.mor₃)⟦-1⟧')⟦1⟧'` with `T.mor₃` up to the canonical conjugating isomorphism. The composite
therefore becomes `T.mor₃ ≫ β'` for a morphism `β' : X⟦1⟧ ⟶ b` obtained by conjugating
`e.hom.app X ≫ α` by these shift isomorphisms. By the hypothesis (`h* = 0`), `T.mor₃ ≫ β' = 0`,
which gives the claim.

(Equivalently, and more cleanly: transport `e.hom.app X ≫ α : (X⟦1⟧)⟦-1⟧ ⟶ b` through the
adjunction `shiftFunctor (-1) ⊣ shiftFunctor 1` — the `homEquiv` of `(shiftEquiv D 1)` — to a
map `X⟦1⟧ ⟶ b`, exactly as in `orthShift`; precomposition with `T.mor₃` is then killed by
`h* = 0`, and naturality of the adjunction unit returns the original composite.)

This is a finite, mechanical chain of shift-naturality rewrites; it introduces no new
mathematical input beyond the definitional unfolding of `invRotate.mor₁` and `h* = 0`.

Strategy for the formal phase: `rw` the definitional form of `T.invRotate.mor₁`
(`= -(T.mor₃)⟦(-1:ℤ)⟧' ≫ (shiftFunctorCompIsoId D 1 (-1) (by ring)).hom.app T.obj₁`, closes by
`rfl`); `rw [Preadditive.neg_comp, Category.assoc, neg_eq_zero]`; then
`apply (shiftFunctor D (1:ℤ)).map_injective` and discharge with
`Functor.map_comp`/`Functor.map_zero`, the naturality of `shiftFunctorCompIsoId D 1 (-1)`
(and `shiftFunctorCompIsoId D (-1) 1`), and `claimB`. -/
theorem invRotate_mor₁_comp_eq_zero (B : D → Prop)
    (T : Triangle D) (b : D)
    (hb1 : B ((shiftFunctor D (1 : ℤ)).obj b))
    (claimB : ∀ (b' : D), B b' →
      ∀ (β : (shiftFunctor D 1).obj T.obj₁ ⟶ b'), T.mor₃ ≫ β = 0)
    (α : T.obj₁ ⟶ b) : T.invRotate.mor₁ ≫ α = 0 := by
  -- SANITY CHECK PASSED (no counterexample). The shift-adjunction transport of
  -- `e.hom.app X ≫ α` lands in `Hom(X⟦1⟧, b⟦1⟧)`, so `claimB` is applied at `b' = b⟦1⟧`,
  -- which is in `B` by shift invariance (hypothesis `hb1`).
  have hdef : T.invRotate.mor₁ =
      -(shiftFunctor D (-1:ℤ)).map T.mor₃ ≫
        (shiftFunctorCompIsoId D 1 (-1) (by ring)).hom.app T.obj₁ := rfl
  rw [hdef, Preadditive.neg_comp, Category.assoc, neg_eq_zero]
  have hnat := (shiftFunctorCompIsoId D (1:ℤ) (-1) (by ring)).hom.naturality α
  simp only [Functor.comp_map, Functor.id_map] at hnat
  rw [← hnat, ← Category.assoc, ← Functor.map_comp]
  have hinner : T.mor₃ ≫ (shiftFunctor D (1:ℤ)).map α = 0 :=
    claimB ((shiftFunctor D (1:ℤ)).obj b) hb1 ((shiftFunctor D (1:ℤ)).map α)
  rw [hinner, Functor.map_zero, zero_comp]

-- Main Statement(s)

/-- **Theorem (Stacks Tag 0H0M, Lemma 13.40.3).**
Let `B ⊂ D` be a full subcategory invariant under all shifts, and let
`X --f--> Y --g--> Z --h--> X[1]` be a distinguished triangle. Then `X` lies in the left
orthogonal `ᗮB` if and only if, for every object `B` of `B`, the precomposition map
`g* : Hom_D(Z, B) → Hom_D(Y, B)` is bijective. -/
@[stacks 0H0M]
theorem isLeftOrthogonal_iff_bijective_precompMap
    (B : D → Prop) (hB : ShiftInvariant B)
    (T : Triangle D) (hT : T ∈ distinguishedTriangles) :
    IsLeftOrthogonal B T.obj₁ ↔
      ∀ (b : D), B b → Function.Bijective (precompMap T b) := by
  constructor
  · -- Forward direction (1) ⇒ (2).
    -- Apply `Hom(-, b)` to the triangle. Orthogonality of `X` (and its shifts) kills
    -- `Hom(X⟦1⟧, b)` and `Hom(X, b)`, so the long exact sequence forces `g*` to be both
    -- injective and surjective.
    intro hX b hb
    constructor
    · -- injective: if `g ≫ φ = g ≫ ψ` then `g ≫ (φ-ψ) = 0`, so by exactness at `Z`
      -- (`yoneda_exact₃`) `φ-ψ = h ≫ g'` with `g' : X⟦1⟧ ⟶ b`; `orthShift` makes `g' = 0`.
      intro φ ψ hφψ
      have hsub : T.mor₂ ≫ (φ - ψ) = 0 := by
        simp only [Preadditive.comp_sub]
        rw [show T.mor₂ ≫ φ = precompMap T b φ from rfl,
            show T.mor₂ ≫ ψ = precompMap T b ψ from rfl, hφψ, sub_self]
      obtain ⟨g', hg'⟩ := Triangle.yoneda_exact₃ T hT (φ - ψ) hsub
      have hg'0 : g' = 0 := orthShift B hB T.obj₁ hX 1 b hb g'
      rw [hg'0, comp_zero] at hg'
      exact sub_eq_zero.mp hg'
    · -- surjective: for `ψ : Y ⟶ b`, `f ≫ ψ = 0` (orthogonality), so by exactness at `Y`
      -- (`yoneda_exact₂`) `ψ = g ≫ φ`, i.e. `ψ = precompMap T b φ`.
      intro ψ
      have hz : T.mor₁ ≫ ψ = 0 := hX b hb (T.mor₁ ≫ ψ)
      obtain ⟨φ, hφ⟩ := Triangle.yoneda_exact₂ T hT ψ hz
      exact ⟨φ, hφ.symm⟩
  · -- Backward direction (2) ⇒ (1): show `α = 0` for every `α : X ⟶ b`, `b ∈ B`.
    intro hbij b hb α
    -- Claim A: `f* = 0`. For `ψ : Y ⟶ b'`, surjectivity of `g*` lifts `ψ = g ≫ φ`, and
    -- `f ≫ g = 0` (`comp_distTriang_mor_zero₁₂`) gives `f ≫ ψ = 0`.
    have claimA : ∀ (b' : D), B b' → ∀ (ψ : T.obj₂ ⟶ b'), T.mor₁ ≫ ψ = 0 := by
      intro b' hb' ψ
      obtain ⟨φ, hφ⟩ := (hbij b' hb').2 ψ
      rw [show precompMap T b' φ = T.mor₂ ≫ φ from rfl] at hφ
      rw [← hφ, ← Category.assoc, comp_distTriang_mor_zero₁₂ T hT, zero_comp]
    -- Claim B: `h* = 0`. For `β : X⟦1⟧ ⟶ b'`, `g ≫ (h ≫ β) = 0`
    -- (`comp_distTriang_mor_zero₂₃`), so `g* (h ≫ β) = g* 0`; injectivity of `g*` gives
    -- `h ≫ β = 0`.
    have claimB : ∀ (b' : D), B b' →
        ∀ (β : (shiftFunctor D 1).obj T.obj₁ ⟶ b'), T.mor₃ ≫ β = 0 := by
      intro b' hb' β
      have hcomp : T.mor₂ ≫ (T.mor₃ ≫ β) = 0 := by
        rw [← Category.assoc, comp_distTriang_mor_zero₂₃ T hT, zero_comp]
      have hzero : T.mor₂ ≫ (T.mor₃ ≫ β) = T.mor₂ ≫ (0 : T.obj₃ ⟶ b') := by
        rw [hcomp, comp_zero]
      have hinj := (hbij b' hb').1
      have : precompMap T b' (T.mor₃ ≫ β) = precompMap T b' 0 := hzero
      exact hinj this
    -- The inverse-rotated triangle `Z⟦-1⟧ --m₁--> X --f--> Y --g--> Z` is distinguished.
    -- `m₁ ≫ α = 0` (the inverse-rotation gap, killed by `claimB`), so by exactness at `X`
    -- (`yoneda_exact₂` on `T.invRotate`) `α = m₂ ≫ g' = f ≫ g'`, and `claimA` makes it `0`.
    have hT' : T.invRotate ∈ distinguishedTriangles := inv_rot_of_distTriang T hT
    have hm1 : T.invRotate.mor₁ ≫ α = 0 :=
      invRotate_mor₁_comp_eq_zero B T b (hB b hb 1) claimB α
    obtain ⟨g', hg'⟩ := Triangle.yoneda_exact₂ T.invRotate hT' α hm1
    rw [show T.invRotate.mor₂ = T.mor₁ from rfl] at hg'
    rw [hg', claimA b hb g']

end Stacks.Triangulated.AdmissibleSubcategories

end

end
