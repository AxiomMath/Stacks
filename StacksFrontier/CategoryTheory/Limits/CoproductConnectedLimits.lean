module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Sheafification
public import StacksFrontier.CategoryTheory.Filtered.AlmostDirected

/-!
# Coproducts commute with finite connected limits

A coproduct is a colimit over a discrete index category, and a discrete category is
almost-directed in the sense of Stacks 002X: its connected components are its objects, each of
which carries only its identity and is therefore a filtered category. So Stacks 002Y, in the form
`CategoryTheory.Limits.preservesLimitsOfShape_colim_of_isConnected`, says that coproducts of sets
commute with finite connected limits.

The statement propagates to presheaves of sets, where colimits are computed pointwise, and from
there to sheaves of sets, where a colimit is the sheafification of the colimit of presheaves and
sheafification is left exact.

Connectedness of the limit shape is essential at every stage: for the discrete two-object shape
the claim would read `∐ᵢ (Aᵢ × Bᵢ) ≅ (∐ᵢ Aᵢ) × (∐ᵢ Bᵢ)`.

## Main results

* `CategoryTheory.Limits.isAlmostDirected_discrete`: a discrete category is almost-directed.
* `CategoryTheory.Limits.preservesLimitsOfShape_colim_discrete`: coproducts of sets commute with
  finite connected limits.
* `CategoryTheory.Limits.preservesLimitsOfShape_colim_discrete_functor` and
  `CategoryTheory.Limits.preservesLimitsOfShape_colim_discrete_sheaf`: the same for presheaves
  and for sheaves of sets.
* `CategoryTheory.Limits.preservesLimitsOfShape_sigma`: a coproduct of functors each of which
  commutes with limits of a given shape commutes with limits of that shape, as soon as the
  colimit functor over the discrete index does.

## References

* [Stacks Project, Tag 002X](https://stacks.math.columbia.edu/tag/002X)
* [Stacks Project, Tag 002Y](https://stacks.math.columbia.edu/tag/002Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits

universe w v₁ u₁ v₂ u₂ t ℓ

/-- A discrete category is **almost-directed**: a zigzag in a discrete category forces equality,
so each connected component has exactly one object, whose only endomorphism is its identity, and
a one-object category with only its identity is filtered. -/
instance isAlmostDirected_discrete (ι : Type u₁) : IsAlmostDirected (Discrete ι) where
  isFiltered_component c := by
    have hobj : ∀ X Y : c.Component, X = Y := by
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      have hz : Zigzag x y := Quotient.exact' (hx.trans hy.symm)
      obtain rfl : x = y := Discrete.ext (eq_of_zigzag ι hz)
      rfl
    have : IsFilteredOrEmpty c.Component :=
      { cocone_objs := fun X Y => ⟨X, 𝟙 X, eqToHom (hobj Y X), trivial⟩
        cocone_maps := fun {X Y} f g => ⟨Y, 𝟙 Y, by
          have h : f = g := c.ι.map_injective (Subsingleton.elim _ _)
          rw [h]⟩ }
    exact { }

/-- **Coproducts of sets commute with finite connected limits**: the case of a discrete index
category of `CategoryTheory.Limits.preservesLimitsOfShape_colim_of_isConnected`, which is
Stacks 002Y. -/
theorem preservesLimitsOfShape_colim_discrete (ι : Type t) [Small.{w} ι]
    (L : Type ℓ) [SmallCategory L] [FinCategory L] [IsConnected L] :
    PreservesLimitsOfShape L (colim : (Discrete ι ⥤ Type w) ⥤ Type w) :=
  have : Small.{w} (Discrete ι) := small_map discreteEquiv
  preservesLimitsOfShape_colim_of_isConnected (Discrete ι) L

/-- Coproducts of presheaves of sets commute with finite connected limits: colimits in a category
of functors to sets are computed pointwise, so this is
`CategoryTheory.Limits.preservesLimitsOfShape_colim_discrete` at each object. -/
theorem preservesLimitsOfShape_colim_discrete_functor
    (D : Type u₁) [Category.{v₁} D] (ι : Type t) [Small.{w} ι]
    (L : Type ℓ) [SmallCategory L] [FinCategory L] [IsConnected L] :
    PreservesLimitsOfShape L (colim : (Discrete ι ⥤ D ⥤ Type w) ⥤ (D ⥤ Type w)) := by
  refine preservesLimitsOfShape_of_evaluation _ L fun V => ?_
  have := preservesLimitsOfShape_colim_discrete.{w} ι L
  exact preservesLimitsOfShape_of_natIso
    (preservesColimitNatIso ((evaluation D (Type w)).obj V)).symm

/-- Coproducts of sheaves of sets commute with finite connected limits.

A colimit of sheaves is the sheafification of the colimit of the underlying presheaves: the
sheafification functor preserves colimits, being a left adjoint, and is inverse to the inclusion
on sheaves. The inclusion preserves all limits, the presheaf colimit commutes with finite
connected limits by
`CategoryTheory.Limits.preservesLimitsOfShape_colim_discrete_functor`, and sheafification is left
exact. -/
theorem preservesLimitsOfShape_colim_discrete_sheaf
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    (ι : Type t) [Small.{w} ι] [HasSheafify J (Type w)]
    [HasColimitsOfShape (Discrete ι) (Sheaf J (Type w))]
    (L : Type ℓ) [SmallCategory L] [FinCategory L] [IsConnected L] :
    PreservesLimitsOfShape L (colim : (Discrete ι ⥤ Sheaf J (Type w)) ⥤ Sheaf J (Type w)) := by
  let i := sheafToPresheaf J (Type w)
  let a := presheafToSheaf J (Type w)
  have : PreservesColimitsOfShape (Discrete ι) a :=
    (sheafificationAdjunction J (Type w)).leftAdjoint_preservesColimits.preservesColimitsOfShape
  -- `i ⋙ a ≅ 𝟭`, the counit of the sheafification adjunction.
  have : IsIso (sheafificationAdjunction J (Type w)).counit :=
    NatIso.isIso_of_isIso_app _
  let hcounit : i ⋙ a ≅ 𝟭 (Sheaf J (Type w)) :=
    asIso (sheafificationAdjunction J (Type w)).counit
  let W := (Functor.whiskeringRight (Discrete ι) (Sheaf J (Type w)) (Cᵒᵖ ⥤ Type w)).obj i
  -- The comparison of the two colimit functors.
  let e : W ⋙ (colim : (Discrete ι ⥤ Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)) ⋙ a ≅
      (colim : (Discrete ι ⥤ Sheaf J (Type w)) ⥤ Sheaf J (Type w)) :=
    Functor.isoWhiskerLeft W (preservesColimitNatIso a) ≪≫
      Functor.isoWhiskerRight
        ((Functor.whiskeringRight (Discrete ι) (Sheaf J (Type w)) (Sheaf J (Type w))).mapIso
          hcounit) colim ≪≫
      Functor.isoWhiskerRight (Iso.refl _) colim
  have := preservesLimitsOfShape_colim_discrete_functor.{w} Cᵒᵖ ι L
  exact preservesLimitsOfShape_of_natIso e

/-- A coproduct of functors each of which commutes with limits of shape `L` commutes with limits
of shape `L`, as soon as the colimit functor over the discrete index category does.

The coproduct is the colimit of the discrete diagram of the factors, and
`CategoryTheory.Limits.colimitIsoFlipCompColim` identifies it with the flipped diagram followed
by that colimit functor; the flipped diagram preserves `L`-limits because its composite with
evaluation at an index is the corresponding factor. -/
theorem preservesLimitsOfShape_sigma
    {A : Type u₂} [Category.{v₂} A] {B : Type u₁} [Category.{v₁} B]
    {ι : Type t} (F : ι → (A ⥤ B))
    (L : Type ℓ) [SmallCategory L] [FinCategory L] [IsConnected L]
    [HasColimitsOfShape (Discrete ι) B]
    [PreservesLimitsOfShape L (colim : (Discrete ι ⥤ B) ⥤ B)]
    [∀ i, PreservesLimitsOfShape L (F i)] :
    PreservesLimitsOfShape L (∐ F) := by
  have : PreservesLimitsOfShape L (Discrete.functor F).flip := by
    refine preservesLimitsOfShape_of_evaluation _ L fun j => ?_
    obtain ⟨j⟩ := j
    have : PreservesLimitsOfShape L ((Discrete.functor F).obj ⟨j⟩) :=
      inferInstanceAs (PreservesLimitsOfShape L (F j))
    exact preservesLimitsOfShape_of_natIso
      (flipCompEvaluation (Discrete.functor F) ⟨j⟩).symm
  have : PreservesLimitsOfShape L ((Discrete.functor F).flip ⋙ colim) :=
    comp_preservesLimitsOfShape _ _
  exact preservesLimitsOfShape_of_natIso (colimitIsoFlipCompColim (Discrete.functor F)).symm

end CategoryTheory.Limits

end
