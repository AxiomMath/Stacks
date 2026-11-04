module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsAtClosedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.CategoryTheory.Sites.SliceTopos.OverFunctorIso

/-!
# Fibre products of modifications at finitely many closed points

Let `X` be an algebraic space over a scheme `S` and let `x₁, …, xₙ ∈ |X|` be pairwise distinct
closed points with chosen elementary étale neighborhoods `(Uᵢ, uᵢ) → (X, xᵢ)` as in Stacks 0BH9,
so that no point of `Uᵢ` lies above `x_j` for `j ≠ i`.

This file treats fibre products of modifications, in the setting of Stacks 0BHB. Write `W₀` for
`X ∖ {x₁, …, xₙ}` and `Wᵢ` for `X ∖ {xᵢ}`. An algebraic space over `X` which is unchanged over `Wᵢ`
is in particular unchanged over the smaller `W₀`, and, by the shrinking condition of Stacks 0BH9,
it is also unchanged over all of `U_j` for `j ≠ i`, because `U_j ⟶ X` factors through `Wᵢ`.
Consequently, if `M₁, …, Mₙ` are algebraic spaces over `X` with `Mᵢ` unchanged over `Wᵢ`, then the
fibre product `M₁ ×_X … ×_X Mₙ` is unchanged over `W₀` and its base change to `Uᵢ` is the base
change of `Mᵢ` alone: every other factor contributes a copy of `Uᵢ`.

## Main definitions

* `AlgebraicGeometry.Space.modificationOfLe` is the inclusion of the modifications away from a
  subfunctor into the modifications away from a smaller one.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.openAwayFromSinglePoint` is the open subspace
  `X ∖ {xᵢ}` and `AlgebraicGeometry.Space.ClosedPointNeighborhoods.modificationsAtSinglePoint`
  the category `C_{X, {xᵢ}}` of algebraic spaces over `X` unchanged over it.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.pullbackPiIso` identifies the base change to
  `Uᵢ` of a fibre product of modifications, the `j`th away from `X ∖ {x_j}`, with the base change
  of the `i`th factor.

## Main results

* `AlgebraicGeometry.Space.isTerminalPullbackObj` and
  `AlgebraicGeometry.Space.isIso_pullback_snd_of_isTerminal`: a morphism of presheaves is an
  isomorphism over a subfunctor exactly when its base change to that subfunctor is terminal in
  the slice category.
* `AlgebraicGeometry.Space.isModification_of_le`: a modification away from a subfunctor is a
  modification away from any smaller subfunctor.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.isTerminal_pullback_toSpaceHom_of_ne`: a
  modification of `X` away from `X ∖ {xᵢ}` is an isomorphism over `U_j` for every `j ≠ i`.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.isModification_pi`: a finite fibre product of
  modifications, the `i`th away from `X ∖ {xᵢ}`, is a modification away from `X ∖ {x₁, …, xₙ}`.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.essSurj_restrictionFunctor`: the functor of
  Stacks 0BHA is essentially surjective as soon as each of its single-point counterparts is.

## Implementation notes

The condition `IsIso (pullback.snd g W₀.ι)` cutting out a modification is used throughout in the
equivalent form `IsTerminal ((Over.pullback W₀.ι).obj g)`. In that form it is manifestly stable
under the limits of the slice category: `CategoryTheory.Over.pullback` has
`CategoryTheory.Over.map` as a left adjoint, hence preserves products, and a product of terminal
objects is terminal.

## References

* [Stacks Project, Tag 0BH9](https://stacks.math.columbia.edu/tag/0BH9)
* [Stacks Project, Tag 0BHA](https://stacks.math.columbia.edu/tag/0BHA)
* [Stacks Project, Tag 0BHB](https://stacks.math.columbia.edu/tag/0BHB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Terminal objects of slice categories -/

/-- An object of a slice category whose structure morphism is an isomorphism is terminal: it is
then isomorphic to the identity, which is the terminal object. -/
def isTerminalOverOfIsIsoHom {C : Type*} [Category C] {X : C} (T : Over X)
    (h : IsIso T.hom) : IsTerminal T :=
  letI := h
  Limits.IsTerminal.ofIso Over.mkIdTerminal (Over.isoMk (asIso T.hom).symm (by simp))

/-- A product of terminal objects is terminal. -/
private def isTerminalPi {C : Type*} [Category C] {β : Type*} (M : β → C) [HasProduct M]
    (h : ∀ b, IsTerminal (M b)) : IsTerminal (∏ᶜ M) :=
  Limits.IsTerminal.ofUniqueHom (fun Z ↦ Pi.lift fun b ↦ (h b).from Z)
    fun _ _ ↦ Pi.hom_ext _ _ fun b ↦ (h b).hom_ext _ _

/-- If every factor of a product other than the `b₀`th is terminal, the `b₀`th projection is an
isomorphism. -/
def piIsoOfOthersTerminal {C : Type*} [Category C] {β : Type*} [DecidableEq β]
    (M : β → C) [HasProduct M] (b₀ : β) (h : ∀ b, b ≠ b₀ → IsTerminal (M b)) :
    (∏ᶜ M) ≅ M b₀ where
  hom := Pi.π M b₀
  inv := Pi.lift fun b ↦ if hb : b = b₀ then eqToHom (congrArg M hb).symm
    else (h b hb).from (M b₀)
  hom_inv_id := by
    refine Pi.hom_ext _ _ fun b ↦ ?_
    by_cases hb : b = b₀
    · subst hb; simp
    · exact (h b hb).hom_ext _ _
  inv_hom_id := by simp

/-- An isomorphism in a product of categories is a family of isomorphisms. -/
private def piIso {I : Type*} {C : I → Type*} [∀ i, Category (C i)] {X Y : ∀ i, C i}
    (e : ∀ i, X i ≅ Y i) : X ≅ Y where
  hom i := (e i).hom
  inv i := (e i).inv
  hom_inv_id := by funext i; exact (e i).hom_inv_id
  inv_hom_id := by funext i; exact (e i).inv_hom_id

/-- A finite product indexed by `Fin (n + 1)` splits off its zeroth factor. -/
private def piFinSuccIso {C : Type*} [Category C] [HasFiniteProducts C] {n : ℕ}
    (M : Fin (n + 1) → C) : (∏ᶜ M) ≅ M 0 ⨯ ∏ᶜ fun i : Fin n ↦ M i.succ where
  hom := prod.lift (Pi.π M 0) (Pi.lift fun i ↦ Pi.π M i.succ)
  inv := Pi.lift fun i ↦
    Fin.cases (motive := fun i ↦ (M 0 ⨯ ∏ᶜ fun j : Fin n ↦ M j.succ) ⟶ M i)
      prod.fst (fun j ↦ prod.snd ≫ Pi.π (fun j : Fin n ↦ M j.succ) j) i
  hom_inv_id := by
    refine Pi.hom_ext _ _ fun i ↦ ?_
    induction i using Fin.cases <;> simp
  inv_hom_id := by
    refine prod.hom_ext ?_ (Pi.hom_ext _ _ fun j ↦ ?_) <;> simp

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Slice categories of presheaves over the big fppf site have finite products, the ambient
category having all finite limits. -/
instance hasFiniteProducts_over {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} :
    HasFiniteProducts (Over W) :=
  Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

variable {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A morphism of presheaves which becomes an isomorphism after base change along `p` has that
base change terminal in the slice category over the source of `p`. -/
def isTerminalPullbackObj {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : V ⟶ W) (X : Over W)
    (h : IsIso (pullback.snd X.hom p)) : IsTerminal ((Over.pullback p).obj X) :=
  isTerminalOverOfIsIsoHom _ h

/-- Conversely, a base change along `p` which is terminal in the slice category over the source
of `p` is an isomorphism. -/
theorem isIso_pullback_snd_of_isTerminal {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : V ⟶ W)
    (X : Over W) (h : IsTerminal ((Over.pullback p).obj X)) : IsIso (pullback.snd X.hom p) :=
  Over.isIso_hom_of_isTerminal h

/-- Terminality of a base change propagates along a factorisation: if the base change of `X` along
`p` is terminal, so is its base change along `q ≫ p`. -/
def isTerminalPullbackObjOfFactor {V₁ V₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : V₁ ⟶ W) (q : V₂ ⟶ V₁) (X : Over W)
    (h : IsTerminal ((Over.pullback p).obj X)) :
    IsTerminal ((Over.pullback (q ≫ p)).obj X) :=
  Limits.IsTerminal.ofIso (h.isTerminalObj (Over.pullback q) _)
    ((Over.pullbackComp q p).app X).symm

/-- If the base change of `X` along `p` is an isomorphism, so is its base change along any
`r = g ≫ p`. -/
private theorem isIso_pullback_snd_comp_of_isIso {V₁ V₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : V₁ ⟶ W) (g : V₂ ⟶ V₁) (r : V₂ ⟶ W) (hg : g ≫ p = r) (X : Over W)
    (h : IsIso (pullback.snd X.hom p)) : IsIso (pullback.snd X.hom r) := by
  rw [← hg]
  exact isIso_pullback_snd_of_isTerminal B S hS _ X
    (isTerminalPullbackObjOfFactor B S hS _ _ X (isTerminalPullbackObj B S hS p X h))

/-! ### Modifications away from a smaller subfunctor -/

/-- Being a modification away from a subfunctor passes to any smaller subfunctor: an isomorphism
over the larger one restricts to an isomorphism over the smaller one. -/
theorem isModification_of_le {W₀ W₁ : Subfunctor W} (hle : W₁ ≤ W₀) {X : Over W}
    (hX : IsModification B S hS W₀ X) : IsModification B S hS W₁ X := by
  exact ⟨hX.1, isIso_pullback_snd_comp_of_isIso B S hS W₀.ι
    (Subfunctor.lift W₁.ι (by rw [Subfunctor.range_ι]; exact hle)) _ (Subfunctor.lift_ι _ _) X
    hX.2⟩

/-- The inclusion of the modifications away from a subfunctor into the modifications away from a
smaller one. -/
def modificationOfLe {W₀ W₁ : Subfunctor W} (hle : W₁ ≤ W₀) :
    Modification B S hS W₀ ⥤ Modification B S hS W₁ :=
  ObjectProperty.lift _ (ObjectProperty.ι (IsModification B S hS W₀))
    fun M ↦ isModification_of_le B S hS hle M.property

/-! ### Algebraicity of a finite fibre product -/

/-- The underlying presheaf of a finite fibre product of algebraic spaces over an algebraic space
is an algebraic space. -/
theorem isAlgebraicSpace_left_pi (hW : IsAlgebraicSpace B S hS W) :
    ∀ (n : ℕ) (M : Fin n → Over W), (∀ i, IsAlgebraicSpace B S hS (M i).left) →
      IsAlgebraicSpace B S hS (∏ᶜ M : Over W).left := by
  intro n
  induction n with
  | zero =>
    intro M _
    have ht : IsTerminal (∏ᶜ M : Over W) := isTerminalPi M fun i ↦ i.elim0
    exact AlgebraicGeometry.isAlgebraicSpace_of_iso B S hS
      ((Over.forget W).mapIso (ht.uniqueUpToIso Over.mkIdTerminal)) hW
  | succ n ih =>
    intro M hM
    exact AlgebraicGeometry.isAlgebraicSpace_of_iso B S hS
      ((Over.forget W).mapIso (piFinSuccIso M) ≪≫ Over.prodLeftIsoPullback _ _)
      (isAlgebraicSpace_pullback B S hS _ _ (hM 0) (ih (fun i ↦ M i.succ) fun i ↦ hM i.succ) hW)

namespace ClosedPointNeighborhoods

variable {B S hS} {n : ℕ} (D : ClosedPointNeighborhoods B S hS n)

/-! ### The open subspace away from a single chosen point -/

/-- The open subspace `X ∖ {xᵢ}` of the space, cut out by the complement of the `i`th chosen
point. -/
def openAwayFromSinglePoint (i : Fin n) : Subfunctor D.space.obj :=
  openSubspaceOfPoints B S hS D.space.obj {D.point i}ᶜ

/-- The point set of `X ∖ {xᵢ}` is the complement of the `i`th chosen point. -/
theorem range_pointsMap_ι_openAwayFromSinglePoint (i : Fin n) :
    Set.range (pointsMap B S hS (D.openAwayFromSinglePoint i).toFunctor
      (D.openAwayFromSinglePoint i).ι) = {D.point i}ᶜ :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS _

/-- `X ∖ {xᵢ}` is an open subspace of the space, the chosen points being closed. -/
theorem isOpenSubspace_openAwayFromSinglePoint (i : Fin n) :
    IsOpenSubspace B S hS (D.openAwayFromSinglePoint i) :=
  isOpenSubspace_openSubspaceOfPoints B S hS D.space.property _
    (D.isClosed_point i).isOpen_compl

/-- `X ∖ {x₁, …, xₙ}` is contained in `X ∖ {xᵢ}`. -/
theorem openAwayFromPoints_le_openAwayFromSinglePoint (i : Fin n) :
    D.openAwayFromPoints ≤ D.openAwayFromSinglePoint i := by
  have hsub : (Set.range D.point)ᶜ ⊆ ({D.point i} : Set (points B S hS D.space.obj))ᶜ :=
    Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 ⟨i, rfl⟩)
  intro U x hx
  exact Set.Subset.trans hx hsub

/-- **Stacks 0BHA** at a single point: the category `C_{X, {xᵢ}}` of algebraic spaces over `X`
which are unchanged over `X ∖ {xᵢ}`. -/
abbrev modificationsAtSinglePoint (i : Fin n) :=
  Modification B S hS (D.openAwayFromSinglePoint i)

/-- The inclusion `C_{X, {xᵢ}} ⥤ C_{X, {x₁, …, xₙ}}`: a space over `X` unchanged over
`X ∖ {xᵢ}` is unchanged over the smaller `X ∖ {x₁, …, xₙ}`. -/
def modificationsAtSinglePointToAwayFromPoints (i : Fin n) :
    D.modificationsAtSinglePoint i ⥤ D.modificationsAwayFromPoints :=
  modificationOfLe B S hS (D.openAwayFromPoints_le_openAwayFromSinglePoint i)

/-! ### The shrinking condition of Stacks 0BH9 -/

/-- For `j ≠ i` the morphism `U_j ⟶ X` factors through `X ∖ {xᵢ}`: after the shrinking of
Stacks 0BH9 no point of `U_j` lies above `xᵢ`. -/
theorem exists_factor_openAwayFromSinglePoint {i j : Fin n} (hij : i ≠ j) :
    ∃ g : (D.neighborhoodSpace j).obj ⟶ (D.openAwayFromSinglePoint i).toFunctor,
      g ≫ (D.openAwayFromSinglePoint i).ι = (D.toSpaceHom j).hom := by
  refine (factorsThrough_openSubspace_iff_points B S hS D.space.property
    (D.neighborhoodSpace j).property _ (D.isOpenSubspace_openAwayFromSinglePoint i) _).2 ?_
  rw [D.range_pointsMap_ι_openAwayFromSinglePoint i]
  rintro z ⟨y, rfl⟩
  exact D.map_ne_point j i (Ne.symm hij) y

/-- A modification of `X` away from `X ∖ {xᵢ}` is an isomorphism over the whole of `U_j` for
every `j ≠ i`, because `U_j ⟶ X` factors through `X ∖ {xᵢ}`. -/
theorem isIso_pullback_snd_toSpaceHom_of_ne {i j : Fin n} (hij : i ≠ j) (M : Over D.space.obj)
    (hM : IsModification B S hS (D.openAwayFromSinglePoint i) M) :
    IsIso (pullback.snd M.hom (D.toSpaceHom j).hom) := by
  obtain ⟨g, hg⟩ := D.exists_factor_openAwayFromSinglePoint hij
  exact isIso_pullback_snd_comp_of_isIso B S hS _ g _ hg M hM.2

/-- The base change to `U_j` of a modification of `X` away from `X ∖ {xᵢ}`, `j ≠ i`, is terminal
in the slice category over `U_j`. -/
def isTerminal_pullback_toSpaceHom_of_ne {i j : Fin n} (hij : i ≠ j) (M : Over D.space.obj)
    (hM : IsModification B S hS (D.openAwayFromSinglePoint i) M) :
    IsTerminal ((Over.pullback (D.toSpaceHom j).hom).obj M) :=
  isTerminalPullbackObj B S hS _ M (D.isIso_pullback_snd_toSpaceHom_of_ne hij M hM)

/-! ### Fibre products of modifications at the chosen points -/

/-- A finite fibre product over `X` of algebraic spaces over `X`, the `i`th unchanged over
`X ∖ {xᵢ}`, is unchanged over `X ∖ {x₁, …, xₙ}`. -/
theorem isModification_pi (M : Fin n → Over D.space.obj)
    (hM : ∀ i, IsModification B S hS (D.openAwayFromSinglePoint i) (M i)) :
    IsModification B S hS D.openAwayFromPoints (∏ᶜ M) := by
  refine ⟨isAlgebraicSpace_left_pi B S hS D.space.property n M fun i ↦ (hM i).1,
    isIso_pullback_snd_of_isTerminal B S hS _ _ ?_⟩
  refine Limits.IsTerminal.ofIso (isTerminalPi _ fun i ↦ ?_)
    (PreservesProduct.iso (Over.pullback D.openAwayFromPoints.ι) M).symm
  exact isTerminalPullbackObj B S hS _ _ (isModification_of_le B S hS
    (D.openAwayFromPoints_le_openAwayFromSinglePoint i) (hM i)).2

/-- The base change to `Uᵢ` of a fibre product over `X` of algebraic spaces over `X`, the `j`th
unchanged over `X ∖ {x_j}`, is the base change of the `i`th factor alone: the other factors are
already isomorphisms over `Uᵢ`. -/
def pullbackPiIso (M : Fin n → Over D.space.obj)
    (hM : ∀ i, IsModification B S hS (D.openAwayFromSinglePoint i) (M i)) (i : Fin n) :
    (Over.pullback (D.toSpaceHom i).hom).obj (∏ᶜ M) ≅
      (Over.pullback (D.toSpaceHom i).hom).obj (M i) :=
  PreservesProduct.iso (Over.pullback (D.toSpaceHom i).hom) M ≪≫
    piIsoOfOthersTerminal _ i fun j hj ↦
      D.isTerminal_pullback_toSpaceHom_of_ne (i := j) (j := i) hj (M j) (hM j)

/-- The underlying object of a component of the functor of Stacks 0BHA is the base change along
the corresponding neighborhood. -/
theorem restrictionComponent_obj_obj (i : Fin n) (Z : D.modificationsAwayFromPoints) :
    ((D.restrictionComponent i).obj Z).obj =
      (Over.pullback (D.toSpaceHom i).hom).obj Z.obj :=
  rfl

/-- **The reduction of Stacks 0BHB to its single-point case.** If every algebraic space over
`Uᵢ` unchanged over `Uᵢ ∖ {uᵢ}` is the base change of an algebraic space over `X` unchanged over
`X ∖ {xᵢ}`, then the functor `F` of Stacks 0BHA is essentially surjective. -/
theorem essSurj_restrictionFunctor
    (hsingle : ∀ (i : Fin n) (N : D.modificationsAt i),
      ∃ M : D.modificationsAtSinglePoint i,
        Nonempty ((Over.pullback (D.toSpaceHom i).hom).obj M.obj ≅ N.obj)) :
    D.restrictionFunctor.EssSurj := by
  refine ⟨fun N ↦ ?_⟩
  choose M e using fun i ↦ hsingle i (N i)
  refine ⟨⟨∏ᶜ fun i ↦ (M i).obj, D.isModification_pi _ fun i ↦ (M i).property⟩,
    ⟨piIso fun i ↦ (ObjectProperty.ι (IsModification B S hS (D.openAwayFromPoint i))).preimageIso
      (D.pullbackPiIso (fun j ↦ (M j).obj) (fun j ↦ (M j).property) i ≪≫ (e i).some)⟩⟩

end ClosedPointNeighborhoods

end AlgebraicGeometry.Space

end
