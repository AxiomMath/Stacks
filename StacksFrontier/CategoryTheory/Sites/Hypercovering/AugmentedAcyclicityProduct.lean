module

public import Mathlib.CategoryTheory.Limits.Connected
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Coskeletal
public import StacksFrontier.CategoryTheory.Sites.CoveringPermanence
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.AugmentedAcyclicity
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.FreeAbelianResolutionKInjective
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Map
public import StacksFrontier.CategoryTheory.Sites.LocallySurjectiveBaseChange

/-!
# Multiplying an augmented simplicial presheaf by a fixed presheaf of sets

Stacks 01GE says that the homology sheaves of `s(ℤ_A^♯)` vanish in positive degrees, for an
augmented simplicial presheaf of sets `A` whose degree-zero augmentation, relation map and
matching maps are locally surjective. This module carries that statement over to the base change
along a presheaf of sets `T`: the augmented simplicial presheaf `T × A`, with
`(T × A)_n = T × A_n` and augmentation `T × A_0 ⟶ T × A.right`, satisfies the same three
hypotheses, with no hypothesis at all on `T`, so Stacks 01GE holds for it.

The point of the construction is that `ℤ_{T × A}^♯` is `ℤ_A^♯` with coefficients in `ℤ_T^♯`: at
`T = h_V` representable, `ℤ_{h_V × A_n}^♯` is `ℤ_{A_n}^♯ ⊗ ℤ_V^♯`, so Stacks 01GE applied to
`h_V × A` is Stacks 01GE with coefficients in `ℤ_V^♯` — the one coefficient case needed by
`CategoryTheory.SimplicialSiteSituation.Augmentation`
`.InverseImageAcyclicAgainstResolutionConeFreeYoneda`.

## Main definitions

* `CategoryTheory.Limits.prodConstFunctor`: the functor `X ↦ T ⨯ X`.
* `CategoryTheory.SimplicialObject.Augmented.prodConst`: the augmented simplicial presheaf
  `T × A`.

## Main results

* `CategoryTheory.Limits.preservesLimitsOfShape_prodConstFunctor` and
  `.preservesLimitsOfShape_prodConstFunctor_of_small`: `T ⨯ -` preserves connected limits, the
  second at the small shapes a pullback and a coskeleton are indexed by.
* `CategoryTheory.SimplicialObject.Augmented.isLocallySurjective_prodConst_hom_app_zero`: the
  degree-zero augmentation of `T × A` is locally surjective as soon as that of `A` is — the first
  hypothesis of Stacks 01GE for `T × A`.
* `CategoryTheory.SimplicialObject.Augmented.isLocallySurjective_edgesToFiberProduct_prodConst`:
  the relation map of `T × A` is locally surjective as soon as that of `A` is — the second
  hypothesis of Stacks 01GE for `T × A`.
* `CategoryTheory.SimplicialObject.Augmented.isLocallySurjective_coskAdj_unit_app_prodConst`:
  the matching maps of `T × A` are locally surjective as soon as those of `A` are — the third
  hypothesis of Stacks 01GE for `T × A`.
* `CategoryTheory.SimplicialObject.Augmented`
  `.quasiIso_freeAbelianSheafResolutionAugmentation_prodConst`: **Stacks 01GE base-changed along
  a presheaf of sets** — the three hypotheses assembled, so that `s(ℤ_{T × A}^♯)` resolves
  `ℤ_{T × A.right}^♯` whenever `s(ℤ_A^♯)` resolves `ℤ_{A.right}^♯` by Stacks 01GE.

## Implementation notes

`CategoryTheory.Limits.prodConstFunctor` is `Limits.prod.functor.obj T` written out, and
`prodConstFunctor_eq` records that they are equal on the nose. The re-spelling is not cosmetic:
`Limits.prod.functor` is a plain definition, so `(Limits.prod.functor.obj T).obj X` does not
reduce to `T ⨯ X` at the transparency the elaborator uses for type-correctness, and a statement
mixing the two spellings fails to typecheck. Writing the functor out makes `.obj` and `.map`
available by `rfl`, while `prodConstFunctor_eq` keeps every lemma proved about
`Limits.prod.functor.obj T` — in particular `Limits.prod_preservesConnectedLimits` — applicable.

`prodConst` is written out degreewise rather than as
`CategoryTheory.SimplicialObject.Augmented.whiskeringObj` applied to `prodConstFunctor`, so that
`prodConst_left` and `prodConst_hom_app` hold by `rfl`; both it and `prodConstFunctor` are
`implicit_reducible`, without which a statement relating `(prodConst T A).hom.app n` to
`Limits.prod.map (𝟙 T) (A.hom.app n)` is rejected as not type-correct.

Local surjectivity of the degree-zero augmentation is base change: the square identifying
`T ⨯ A_0 ⟶ T ⨯ A.right` as the pullback of `A_0 ⟶ A.right` along the projection is
`Stacks.CategoryTheory.Hypercovering.isPullback_prod_snd`, and the base-change statement is
`CategoryTheory.Presheaf.isLocallySurjective_of_isPullback`.

For the relation map the same base change is applied to `edgesToFiberProduct A` itself, which
needs the relation map of `T × A` to be that of `A` times the identity of `T`. It is, because
`T ⨯ -` preserves the fibre product: `WalkingCospan` is connected, so
`preservesLimitsOfShape_prodConstFunctor_of_small` applies, and `CategoryTheory.IsPullback.map`
then exhibits `T ⨯ (A_0 ×_{A.right} A_0)` as the fibre product of two copies of
`T ⨯ A_0 ⟶ T ⨯ A.right`; `Limits.pullback.hom_ext` identifies the two maps into it.

The matching maps are the same base change, applied to the coskeleton comparison rather than to
a single map. `prodConst_left` is an equality of functors on the nose, so the simplicial presheaf
underlying `T × A` is `A.left ⋙ prodConstFunctor T`, and
`Stacks.CategoryTheory.Hypercovering.exists_iso_map_coskAdj_unit_app` identifies the degree-`n+1`
coskeleton unit of such a composite with the image under the functor of the coskeleton unit of
`A.left`. That comparison asks only that the functor preserve the pointwise right Kan extensions
defining the coskeleton, which `T ⨯ -` does: those are limits over the categories
`StructuredArrow ⦋m⦌ᵒᵖ (Δ_{≤n} ⊆ Δ)ᵒᵖ`, connected for `n ≥ 1` because the truncated inclusion is
then initial, so `CategoryTheory.Functor.preservesPointwiseRightKanExtensions_of_final` applies
to `preservesLimitsOfShape_prodConstFunctor_of_small`. The hypothesis `1 ≤ n` enters only as the
`NeZero n` which `SimplexCategory.Truncated.initial_inclusion` requires.

The universe shift in `preservesLimitsOfShape_prodConstFunctor_of_small` is unavoidable:
`Limits.prod_preservesConnectedLimits` is stated for shapes in the universe of the morphisms of
the ambient category, while `WalkingCospan` and the matching category of a coskeleton are small.
`CategoryTheory.AsSmall.equiv` and `Limits.preservesLimitsOfShape_of_equiv` bridge the two.

## References

* [Stacks Project, Tag 01GE](https://stacks.math.columbia.edu/tag/01GE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w₂ w₁ w v u

namespace CategoryTheory.Limits

variable {D : Type u} [Category.{v} D] [HasBinaryProducts D] (T : D)

/-- The functor `X ↦ T ⨯ X`, written out so that its action on objects and on morphisms is
available by `rfl`. It is `Limits.prod.functor.obj T`; see `prodConstFunctor_eq`. -/
@[simps, implicit_reducible]
def prodConstFunctor : D ⥤ D where
  obj X := T ⨯ X
  map g := Limits.prod.map (𝟙 T) g
  map_id _ := by simp
  map_comp _ _ := by simp

/-- `Limits.prodConstFunctor` is `Limits.prod.functor.obj T`. -/
lemma prodConstFunctor_eq : prodConstFunctor T = Limits.prod.functor.obj T := rfl

/-- **`T ⨯ -` preserves connected limits**, this being
`CategoryTheory.Limits.prod_preservesConnectedLimits` at the `prodConstFunctor` spelling. -/
lemma preservesLimitsOfShape_prodConstFunctor {L : Type v} [SmallCategory L] [IsConnected L] :
    PreservesLimitsOfShape L (prodConstFunctor T) :=
  prod_preservesConnectedLimits T

/-- **`T ⨯ -` preserves connected limits of small shape**, which is the shape of a fibre product
and of the matching category of a coskeleton. -/
lemma preservesLimitsOfShape_prodConstFunctor_of_small {L : Type} [SmallCategory L]
    [IsConnected L] : PreservesLimitsOfShape L (prodConstFunctor T) := by
  have : IsConnected (AsSmall.{v} L) := isConnected_of_equivalent AsSmall.equiv
  have := preservesLimitsOfShape_prodConstFunctor T (L := AsSmall.{v} L)
  exact preservesLimitsOfShape_of_equiv AsSmall.equiv.symm _

end CategoryTheory.Limits

namespace CategoryTheory.SimplicialObject.Augmented

variable {C : Type u} [Category.{v} C] (T : Cᵒᵖ ⥤ Type w)

/-- The naturality of the augmentation of `T × A`. -/
lemma prodConst_naturality (A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w))
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    Limits.prod.map (𝟙 T) (A.left.map φ) ≫ Limits.prod.map (𝟙 T) (A.hom.app m)
      = Limits.prod.map (𝟙 T) (A.hom.app n) ≫ 𝟙 (T ⨯ A.right) := by
  have h : A.left.map φ ≫ A.hom.app m = A.hom.app n := by simp
  simp [h]

/-- The augmented simplicial presheaf `T × A`: in degree `n` it is `T × A_n`, its presheaf of
augmentation points is `T × A.right`, and its augmentation is the product of the augmentation of
`A` with the identity of `T`. -/
@[implicit_reducible]
def prodConst (A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)) :
    SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w) where
  left :=
    { obj := fun n => T ⨯ A.left.obj n
      map := fun φ => Limits.prod.map (𝟙 T) (A.left.map φ)
      map_id := fun _ => by simp
      map_comp := fun _ _ => by simp }
  right := T ⨯ A.right
  hom :=
    { app := fun n => Limits.prod.map (𝟙 T) (A.hom.app n)
      naturality := fun _ _ φ => prodConst_naturality T A φ }

/-- The simplicial presheaf underlying `T × A` is `A` followed by `T ⨯ -`. -/
lemma prodConst_left (A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)) :
    (prodConst T A).left = A.left ⋙ prodConstFunctor T :=
  rfl

/-- The augmentation of `T × A` in each degree is the augmentation of `A` times the identity. -/
lemma prodConst_hom_app (A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)) (n : SimplexCategoryᵒᵖ) :
    (prodConst T A).hom.app n = Limits.prod.map (𝟙 T) (A.hom.app n) :=
  rfl

/-- Local surjectivity is preserved by `f ↦ 𝟙 T ⨯ f`, being a base change along a projection. -/
private theorem isLocallySurjective_prod_map_id (J : GrothendieckTopology C) {X Y : Cᵒᵖ ⥤ Type w}
    (f : X ⟶ Y) [Presheaf.IsLocallySurjective J f] :
    Presheaf.IsLocallySurjective J (Limits.prod.map (𝟙 T) f) :=
  Presheaf.isLocallySurjective_of_isPullback J
    (Stacks.CategoryTheory.Hypercovering.isPullback_prod_snd (B := T) f).flip

/-- **The degree-zero augmentation of `T × A` is locally surjective** as soon as that of `A` is:
it is the base change of the latter along the projection `T × A.right ⟶ A.right`. This is the
first of the three hypotheses of Stacks 01GE for `T × A`. -/
theorem isLocallySurjective_prodConst_hom_app_zero (J : GrothendieckTopology C)
    (A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w))
    (h₀ : Presheaf.IsLocallySurjective J (A.hom.app (op (SimplexCategory.mk 0)))) :
    Presheaf.IsLocallySurjective J ((prodConst T A).hom.app (op (SimplexCategory.mk 0))) := by
  have := h₀
  rw [prodConst_hom_app]
  exact isLocallySurjective_prod_map_id T J _

/-- **The relation map of `T × A` is locally surjective** as soon as that of `A` is: `T ⨯ -`
preserves the fibre product `A_0 ×_{A.right} A_0`, so the relation map of `T × A` is the relation
map of `A` times the identity of `T`, and that is the base change of the relation map of `A`
along the projection. This is the second of the three hypotheses of Stacks 01GE for `T × A`. -/
theorem isLocallySurjective_edgesToFiberProduct_prodConst (J : GrothendieckTopology C)
    (A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w))
    (h₁ : Presheaf.IsLocallySurjective J (edgesToFiberProduct A)) :
    Presheaf.IsLocallySurjective J (edgesToFiberProduct (prodConst T A)) := by
  have := preservesLimitsOfShape_prodConstFunctor_of_small T (L := WalkingCospan)
  set f₀ := A.hom.app (op (SimplexCategory.mk 0)) with hf₀
  have hP : IsPullback (Limits.prod.map (𝟙 T) (Limits.pullback.fst f₀ f₀))
      (Limits.prod.map (𝟙 T) (Limits.pullback.snd f₀ f₀))
      ((prodConst T A).hom.app (op (SimplexCategory.mk 0)))
      ((prodConst T A).hom.app (op (SimplexCategory.mk 0))) :=
    (IsPullback.of_hasPullback f₀ f₀).map (prodConstFunctor T)
  have := isLocallySurjective_prod_map_id T J (edgesToFiberProduct A)
  have h0 : edgesToFiberProduct A ≫ Limits.pullback.fst f₀ f₀ = A.left.δ 0 :=
    Limits.pullback.lift_fst _ _ _
  have h1 : edgesToFiberProduct A ≫ Limits.pullback.snd f₀ f₀ = A.left.δ 1 :=
    Limits.pullback.lift_snd _ _ _
  have key : edgesToFiberProduct (prodConst T A)
      = Limits.prod.map (𝟙 T) (edgesToFiberProduct A) ≫ hP.isoPullback.hom := by
    refine Limits.pullback.hom_ext ?_ ?_
    · rw [edgesToFiberProduct, Limits.pullback.lift_fst, Category.assoc,
        hP.isoPullback_hom_fst]
      show Limits.prod.map (𝟙 T) (A.left.δ 0) = _
      rw [← h0]
      simp
    · rw [edgesToFiberProduct, Limits.pullback.lift_snd, Category.assoc,
        hP.isoPullback_hom_snd]
      show Limits.prod.map (𝟙 T) (A.left.δ 1) = _
      rw [← h1]
      simp
  rw [key]
  infer_instance

/-- **The matching maps of `T × A` are locally surjective** as soon as those of `A` are: the
limits computing the `n`-coskeleton of a simplicial presheaf are indexed by the connected
categories `(Δ/⦋m⦌)_{≤n}`, `n ≥ 1`, so `T ⨯ -` preserves them, and the degree-`n + 1` component
of the coskeleton unit of `T × A` is therefore, after one isomorphism, the component of that of
`A` multiplied by the identity of `T` — which is the base change of the latter along the
projection. This is the third of the three hypotheses of Stacks 01GE for `T × A`. -/
theorem isLocallySurjective_coskAdj_unit_app_prodConst (J : GrothendieckTopology C)
    (A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)) (n : ℕ) (hn : 1 ≤ n)
    (hm : Presheaf.IsLocallySurjective J
      (((SimplicialObject.coskAdj n).unit.app A.left).app
        (op (SimplexCategory.mk (n + 1))))) :
    Presheaf.IsLocallySurjective J
      (((SimplicialObject.coskAdj n).unit.app (prodConst T A).left).app
        (op (SimplexCategory.mk (n + 1)))) := by
  have : NeZero n := ⟨by omega⟩
  have : (prodConstFunctor T).PreservesPointwiseRightKanExtensions
      (SimplexCategory.Truncated.inclusion n).op :=
    Functor.preservesPointwiseRightKanExtensions_of_final _ _
      fun _ _ _ => preservesLimitsOfShape_prodConstFunctor_of_small T
  obtain ⟨e, he⟩ := Stacks.CategoryTheory.Hypercovering.exists_iso_map_coskAdj_unit_app'
    n A.left (prodConstFunctor T) (op (SimplexCategory.mk (n + 1)))
  have : Presheaf.IsLocallySurjective J ((prodConstFunctor T).map
      (((SimplicialObject.coskAdj n).unit.app A.left).app (op (SimplexCategory.mk (n + 1))))) :=
    isLocallySurjective_prod_map_id T J _
  rw [prodConst_left, ← he]
  infer_instance

end CategoryTheory.SimplicialObject.Augmented

namespace CategoryTheory.SimplicialObject.Augmented

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (T : Cᵒᵖ ⥤ Type u)
  (A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type u))

/-- **Stacks 01GE base-changed along a presheaf of sets.** If the degree-zero augmentation, the
relation map and the matching maps of `A` are locally surjective, then the complex
`s(ℤ_{T × A}^♯)` of free abelian sheaves is a resolution of `ℤ_{T × A.right}^♯`, for every
presheaf of sets `T`.

The three hypotheses of Stacks 01GE for `T × A` are
`isLocallySurjective_prodConst_hom_app_zero`,
`isLocallySurjective_edgesToFiberProduct_prodConst` and
`isLocallySurjective_coskAdj_unit_app_prodConst`; nothing is assumed of `T`. -/
theorem quasiIso_freeAbelianSheafResolutionAugmentation_prodConst
    (h₀ : Presheaf.IsLocallySurjective J (A.hom.app (op (SimplexCategory.mk 0))))
    (h₁ : Presheaf.IsLocallySurjective J (edgesToFiberProduct A))
    (hm : ∀ n : ℕ, 1 ≤ n → Presheaf.IsLocallySurjective J
      (((SimplicialObject.coskAdj n).unit.app A.left).app
        (op (SimplexCategory.mk (n + 1))))) :
    QuasiIso (freeAbelianSheafResolutionAugmentation J (prodConst T A)) :=
  quasiIso_freeAbelianSheafResolutionAugmentation J (prodConst T A)
    (isLocallySurjective_prodConst_hom_app_zero T J A h₀)
    (isLocallySurjective_edgesToFiberProduct_prodConst T J A h₁)
    fun n hn => isLocallySurjective_coskAdj_unit_app_prodConst T J A n hn (hm n hn)

end CategoryTheory.SimplicialObject.Augmented

end
