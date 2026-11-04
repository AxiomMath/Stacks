module

public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.HullInstances
public import StacksFrontier.AlgebraicGeometry.ReflexiveOpenEquivalence.Pushforward

/-!
# The reflexive hull commutes with restriction to a large open

Let `X` be an integral locally Noetherian scheme, let `V ⊆ X` be an open whose complement
carries structure-sheaf depth at least two and which is itself integral and locally Noetherian,
and let `ℱ` be a coherent `𝒪_X`-module.  Then

`(ℱ^∨∨)|_V ≅ (ℱ|_V)^∨∨`,

by the isomorphism that carries the canonical map `ℱ|_V ⟶ (ℱ|_V)^∨∨` to the restriction of
`ℱ ⟶ ℱ^∨∨`.

## Main results

* `Stacks.AlgebraicGeometry.ReflexiveModules.restrictReflexiveHullIso`: the isomorphism above.
* `Stacks.AlgebraicGeometry.ReflexiveModules.toDoubleDual_restrictReflexiveHullIso`: its inverse
  carries the canonical map `ℱ|_V ⟶ (ℱ|_V)^∨∨` to the restriction of `ℱ ⟶ ℱ^∨∨`.

## References

* [Stacks Project, Tag 0AVU](https://stacks.math.columbia.edu/tag/0AVU)
* [Stacks Project, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

/-- The hull bijection is precomposition with the canonical map to the double dual. -/
theorem reflexiveHullHomEquiv_apply {Y : Scheme.{u}} (A B : Y.Modules)
    [IsIso (toDoubleDual (dualSheaf (dualSheaf A)))] [IsIso (toDoubleDual B)]
    (g : dualSheaf (dualSheaf A) ⟶ B) :
    reflexiveHullHomEquiv A B g = toDoubleDual A ≫ g := rfl

/-- The canonical map to the double dual followed by the extension of `f` is `f`. -/
private theorem toDoubleDual_comp_reflexiveHullHomEquiv_symm {Y : Scheme.{u}} (A B : Y.Modules)
    [IsIso (toDoubleDual (dualSheaf (dualSheaf A)))] [IsIso (toDoubleDual B)] (f : A ⟶ B) :
    toDoubleDual A ≫ (reflexiveHullHomEquiv A B).symm f = f :=
  (reflexiveHullHomEquiv A B).apply_symm_apply f

variable {X : Scheme.{u}} [AlgebraicGeometry.IsIntegral X] [IsLocallyNoetherian X]
  (V : X.Opens) [AlgebraicGeometry.IsIntegral V.toScheme] [IsLocallyNoetherian V.toScheme]
  (F : X.Modules) [F.IsCoherent]

/-! ### Coherence and reflexivity of restrictions -/

/-- The restriction of a coherent module to an open subscheme is coherent. -/
instance isCoherent_restrict_opens : (F.restrict V.ι).IsCoherent :=
  isCoherent_restrict_of_isOpenImmersion V.ι F inferInstance

/-- The restriction of the reflexive hull is coherent. -/
instance isCoherent_restrict_reflexiveHull : ((reflexiveHull F).restrict V.ι).IsCoherent :=
  isCoherent_restrict_of_isOpenImmersion V.ι (reflexiveHull F) inferInstance

/-- The restriction of the reflexive hull to an open subscheme is reflexive. -/
instance isIso_toDoubleDual_restrict_reflexiveHull :
    IsIso (toDoubleDual ((reflexiveHull F).restrict V.ι)) :=
  isReflexive_restrict_of_isOpenImmersion V.ι (reflexiveHull F) inferInstance
    (isReflexive_reflexiveHull X F)

omit [AlgebraicGeometry.IsIntegral V.toScheme] [IsLocallyNoetherian V.toScheme] in
/-- If the complement of `V` has structure-sheaf depth at least two, the direct image along `V.ι`
of a coherent reflexive module on `V` is reflexive. -/
theorem isIso_toDoubleDual_pushforward
    (hdepth : ∀ x : X, x ∉ (V : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
    (G : V.toScheme.Modules) [G.IsCoherent] (hG : IsReflexive G) :
    IsIso (toDoubleDual ((Scheme.Modules.pushforward V.ι).obj G)) :=
  (isCoherent_and_isReflexive_pushforward X V hdepth G inferInstance hG).2

/-! ### The two comparison morphisms -/

/-- The comparison morphism `(ℱ|_V)^∨∨ ⟶ (ℱ^∨∨)|_V`: the unique morphism out of the hull of
`ℱ|_V` extending the restriction of the canonical map `ℱ ⟶ ℱ^∨∨`. -/
noncomputable def restrictHullToHullRestrict :
    reflexiveHull (F.restrict V.ι) ⟶ (reflexiveHull F).restrict V.ι :=
  (reflexiveHullHomEquiv (F.restrict V.ι) ((reflexiveHull F).restrict V.ι)).symm
    ((Scheme.Modules.restrictFunctor V.ι).map (toDoubleDual F))

/-- The comparison morphism extends the restriction of `ℱ ⟶ ℱ^∨∨`. -/
theorem toDoubleDual_restrictHullToHullRestrict :
    toDoubleDual (F.restrict V.ι) ≫ restrictHullToHullRestrict V F =
      (Scheme.Modules.restrictFunctor V.ι).map (toDoubleDual F) := by
  exact toDoubleDual_comp_reflexiveHullHomEquiv_symm _ _ _

variable (hdepth : ∀ x : X, x ∉ (V : Set X) →
  (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))

include hdepth

/-- The comparison morphism `(ℱ^∨∨)|_V ⟶ (ℱ|_V)^∨∨` corresponding to the canonical map
`ℱ|_V ⟶ (ℱ|_V)^∨∨` under the restriction–pushforward adjunction and the hull bijection on `X`. -/
noncomputable def hullRestrictToRestrictHull :
    (reflexiveHull F).restrict V.ι ⟶ reflexiveHull (F.restrict V.ι) :=
  haveI := isIso_toDoubleDual_pushforward V hdepth (reflexiveHull (F.restrict V.ι))
    (isReflexive_reflexiveHull V.toScheme (F.restrict V.ι))
  ((Scheme.Modules.restrictAdjunction V.ι).homEquiv (reflexiveHull F)
      (reflexiveHull (F.restrict V.ι))).symm
    ((reflexiveHullHomEquiv F
        ((Scheme.Modules.pushforward V.ι).obj (reflexiveHull (F.restrict V.ι)))).symm
      ((Scheme.Modules.restrictAdjunction V.ι).homEquiv F (reflexiveHull (F.restrict V.ι))
        (toDoubleDual (F.restrict V.ι))))

/-- The second comparison morphism takes the restriction of `ℱ ⟶ ℱ^∨∨` to the canonical map
`ℱ|_V ⟶ (ℱ|_V)^∨∨`. -/
theorem restrictFunctor_map_toDoubleDual_hullRestrictToRestrictHull :
    (Scheme.Modules.restrictFunctor V.ι).map (toDoubleDual F) ≫
        hullRestrictToRestrictHull V F hdepth =
      toDoubleDual (F.restrict V.ι) := by
  have := isIso_toDoubleDual_pushforward V hdepth (reflexiveHull (F.restrict V.ι))
    (isReflexive_reflexiveHull V.toScheme (F.restrict V.ι))
  refine ((Scheme.Modules.restrictAdjunction V.ι).homEquiv F
    (reflexiveHull (F.restrict V.ι))).injective ?_
  rw [Adjunction.homEquiv_naturality_left, hullRestrictToRestrictHull, Equiv.apply_symm_apply]
  exact toDoubleDual_comp_reflexiveHullHomEquiv_symm _ _ _

omit [AlgebraicGeometry.IsIntegral V.toScheme] [IsLocallyNoetherian V.toScheme] in
/-- Precomposition with the restriction of `ℱ ⟶ ℱ^∨∨` is injective on morphisms from
`(ℱ^∨∨)|_V` into a coherent reflexive module on `V`. -/
theorem injective_comp_restrictFunctor_map_toDoubleDual (G : V.toScheme.Modules) [G.IsCoherent]
    (hG : IsReflexive G) :
    Function.Injective fun g : (reflexiveHull F).restrict V.ι ⟶ G =>
      (Scheme.Modules.restrictFunctor V.ι).map (toDoubleDual F) ≫ g := by
  have := isIso_toDoubleDual_pushforward V hdepth G hG
  intro g₁ g₂ h
  refine ((Scheme.Modules.restrictAdjunction V.ι).homEquiv (reflexiveHull F) G).injective ?_
  refine (reflexiveHullHomEquiv F ((Scheme.Modules.pushforward V.ι).obj G)).injective ?_
  rw [reflexiveHullHomEquiv_apply, reflexiveHullHomEquiv_apply,
    ← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_left]
  exact congrArg _ h

/-! ### The isomorphism -/

/-- The reflexive hull commutes with restriction to a large open: for a coherent module `ℱ` on an
integral locally Noetherian scheme and an integral locally Noetherian open `V` whose complement
has structure-sheaf depth at least two, `(ℱ^∨∨)|_V ≅ (ℱ|_V)^∨∨`. -/
noncomputable def restrictReflexiveHullIso :
    (reflexiveHull F).restrict V.ι ≅ reflexiveHull (F.restrict V.ι) where
  hom := hullRestrictToRestrictHull V F hdepth
  inv := restrictHullToHullRestrict V F
  hom_inv_id := by
    refine injective_comp_restrictFunctor_map_toDoubleDual V F hdepth
      ((reflexiveHull F).restrict V.ι)
      (isReflexive_restrict_of_isOpenImmersion V.ι (reflexiveHull F) inferInstance
        (isReflexive_reflexiveHull X F)) ?_
    dsimp only
    rw [← Category.assoc, restrictFunctor_map_toDoubleDual_hullRestrictToRestrictHull,
      toDoubleDual_restrictHullToHullRestrict, Category.comp_id]
  inv_hom_id := by
    refine (reflexiveHullHomEquiv (F.restrict V.ι)
      (reflexiveHull (F.restrict V.ι))).injective ?_
    rw [reflexiveHullHomEquiv_apply, reflexiveHullHomEquiv_apply, ← Category.assoc,
      toDoubleDual_restrictHullToHullRestrict,
      restrictFunctor_map_toDoubleDual_hullRestrictToRestrictHull, Category.comp_id]

/-- The inverse of `restrictReflexiveHullIso` carries the canonical map `ℱ|_V ⟶ (ℱ|_V)^∨∨` to the
restriction of `ℱ ⟶ ℱ^∨∨`. -/
theorem toDoubleDual_restrictReflexiveHullIso :
    toDoubleDual (F.restrict V.ι) ≫ (restrictReflexiveHullIso V F hdepth).inv =
      (Scheme.Modules.restrictFunctor V.ι).map (toDoubleDual F) :=
  toDoubleDual_restrictHullToHullRestrict V F

end Stacks.AlgebraicGeometry.ReflexiveModules

end
