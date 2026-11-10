module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Equiv
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Coskeletal
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Skeleton
public import StacksFrontier.Cotangent.StandardResolution

/-!
# Attaching polynomial cells to a simplicial commutative algebra

Fix a simplicial commutative `A`-algebra `P`, a degree `d` and an index type `I`. A cell boundary
of this data is a compatible family of elements of `P` in the degrees below `d`, one for each index
and each non-surjective map onto `⦋d⦌`. Attaching cells along a boundary adjoins, in each degree
`Δ`, one polynomial generator for each index and each surjection `Δ ⟶ ⦋d⦌`, and sends the new
generators to the prescribed elements along the non-surjective maps; the result is again a
simplicial commutative `A`-algebra, receiving `P` and mapping to any `Q` equipped with `I` elements
in degree `d` that match the boundary.

## Main definitions

* `CommAlgCat.CellBoundary` is the attaching data in degree `d` indexed by `I`.
* `CommAlgCat.attachCells` is the simplicial algebra obtained by attaching the cells, and
  `CommAlgCat.attachCellsι` the inclusion of `P` into it.
* `CommAlgCat.cellDesc` is the map out of an attachment prescribed by the images of the new
  generators.

## Main results

* `CommAlgCat.isIso_attachCellsι_app` shows that attaching cells in degree `d` changes nothing in
  the degrees below `d`.
* `CommAlgCat.exists_cellBoundary_of_bijective` produces a cell boundary for `I` prescribed
  elements of `Q` in degree `n + 1`, given that `P ⟶ Q` is bijective in the degrees at most `n`.

## Implementation notes

The index type `I` lives in a universe `v` of its own and the ambient algebra category is
`CommAlgCat.{max u v} A` for `A : Type u`, which is the smallest universe containing both the
polynomial generators and the algebras: at `v = 0` this is the category `CommAlgCat.{u} A` with
generators indexed by `Type`, and at `v = max u v'` it is `CommAlgCat.{max u v'} A` with generators
indexed by `Type (max u v')`.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe u v w

namespace SimplexCategory

/-- A composite of maps of simplices is not surjective as soon as its last factor is not. -/
theorem not_surjective_comp {Δ Δ' Δ'' : SimplexCategory}
    (f : Δ ⟶ Δ') (g : Δ' ⟶ Δ'') (hg : ¬ Function.Surjective g.toOrderHom) :
    ¬ Function.Surjective (f ≫ g).toOrderHom :=
  fun h => hg (Function.Surjective.of_comp h)

end SimplexCategory

namespace SSet

/-- The counit of the `n`-skeleton adjunction is invertible at a simplicial set of dimension at
most `n`. -/
theorem isIso_skAdj_counit_app (X : SSet.{w}) (n : ℕ)
    [SSet.HasDimensionLT X (n + 1)] : IsIso ((SSet.skAdj n).counit.app X) := by
  obtain ⟨e, he⟩ := SSet.exists_iso_skeleton_hom_ι_eq_skAdj_counit X n
  have hs : X.skeleton (n + 1) = ⊤ := by
    apply le_antisymm le_top
    rw [SSet.Subcomplex.le_iff_contains_nonDegenerate]
    intro m x hx
    exact X.mem_skeleton x.1 (X.dim_lt_of_nonDegenerate x (n + 1))
  rw [← he]
  have hi : IsIso (X.skeleton (n + 1)).ι := by
    rw [hs]
    infer_instance
  infer_instance

/-- Composing with a map of simplicial sets that is bijective in the degrees at most `n` is a
bijection on the maps out of the boundary of the `(n + 1)`-simplex. -/
theorem boundary_postcomp_bijective {X Y : SSet.{w}} (f : X ⟶ Y) (n : ℕ)
    (hf : ∀ k, k ≤ n → Function.Bijective (f.app (op ⦋k⦌))) :
    Function.Bijective (fun g : (∂Δ[n + 1] : SSet.{w}) ⟶ X => g ≫ f) := by
  have hi : IsIso ((SSet.truncation n).map f) := by
    have h (Δ : (SimplexCategory.Truncated n)ᵒᵖ) :
        IsIso (((SSet.truncation n).map f).app Δ) := by
      rw [isIso_iff_bijective]
      exact hf Δ.unop.obj.len Δ.unop.property
    exact NatIso.isIso_of_isIso_app _
  have hc := isIso_skAdj_counit_app (∂Δ[n + 1] : SSet.{w}) n
  let e (Z : SSet.{w}) : ((∂Δ[n + 1] : SSet.{w}) ⟶ Z) ≃
      ((SSet.truncation n).obj (∂Δ[n + 1] : SSet.{w}) ⟶ (SSet.truncation n).obj Z) :=
    (Iso.homCongr (asIso ((SSet.skAdj n).counit.app (∂Δ[n + 1] : SSet.{w}))).symm
      (Iso.refl Z)).trans ((SSet.skAdj n).homEquiv _ Z)
  have he (Z : SSet.{w}) (g : (∂Δ[n + 1] : SSet.{w}) ⟶ Z) :
      e Z g = (SSet.truncation n).map g := by
    simp [e, Adjunction.homEquiv_apply]
  have hmap : (fun g : (∂Δ[n + 1] : SSet.{w}) ⟶ X => g ≫ f) =
      fun g => (e Y).symm (e X g ≫ (SSet.truncation n).map f) := by
    funext g
    apply (e Y).injective
    rw [Equiv.apply_symm_apply, he, he, Functor.map_comp]
  rw [hmap]
  exact (e Y).symm.bijective.comp
    ((Iso.homCongr (Iso.refl _) (asIso ((SSet.truncation n).map f))).bijective.comp
      (e X).bijective)

end SSet

namespace CommAlgCat

/-- The new polynomial generators of an attachment of `I` cells in degree `d`, in the degree `Δ`:
one for each index and each surjection `Δ ⟶ ⦋d⦌`. -/
abbrev CellVariable (d : ℕ) (I : Type v) (Δ : SimplexCategory) :=
  I × {α : Δ ⟶ ⦋d⦌ // Function.Surjective α.toOrderHom}

/-- The data of attaching `I` cells to `P` in degree `d`: an element of `P` in the degree `Δ` for
each index and each non-surjective map `Δ ⟶ ⦋d⦌`, compatible with the simplicial structure. -/
structure CellBoundary {A : Type u} [CommRing A]
    (P : SimplicialObject (CommAlgCat.{max u v} A)) (d : ℕ) (I : Type v) where
  /-- The prescribed element of `P` in degree `Δ` at a non-surjective `α : Δ ⟶ ⦋d⦌`. -/
  val : ∀ (Δ : SimplexCategory) (α : Δ ⟶ ⦋d⦌),
    ¬ Function.Surjective α.toOrderHom → I → P.obj (op Δ)
  /-- The prescribed elements are compatible with the simplicial structure of `P`. -/
  naturality : ∀ {Δ Δ' : SimplexCategory} (f : Δ ⟶ Δ') (α : Δ' ⟶ ⦋d⦌)
    (hα : ¬ Function.Surjective α.toOrderHom) (i : I),
    (P.map f.op).hom (val Δ' α hα i) =
      val Δ (f ≫ α) (SimplexCategory.not_surjective_comp f α hα) i

variable {A : Type u} [CommRing A] {P : SimplicialObject (CommAlgCat.{max u v} A)}
  {d : ℕ} {I : Type v}

/-- The value of the `i`-th attached cell along `α : Δ ⟶ ⦋d⦌`: the new generator when `α` is
surjective, and the element prescribed by the boundary otherwise. -/
noncomputable def cellValue (b : CellBoundary P d I) (Δ : SimplexCategory)
    (α : Δ ⟶ ⦋d⦌) (i : I) : MvPolynomial (CellVariable d I Δ) (P.obj (op Δ)) := by
  classical
  exact if h : Function.Surjective α.toOrderHom then MvPolynomial.X (i, ⟨α, h⟩)
    else MvPolynomial.C (b.val Δ α h i)

/-- The simplicial structure map of an attachment: it acts on the coefficients through `P` and
carries the generator of a surjection `α` to the cell value along `f ≫ α`. -/
noncomputable def cellMap (b : CellBoundary P d I)
    {Δ Δ' : SimplexCategory} (f : Δ ⟶ Δ') :
    MvPolynomial (CellVariable d I Δ') (P.obj (op Δ')) →ₐ[A]
      MvPolynomial (CellVariable d I Δ) (P.obj (op Δ)) :=
  MvPolynomial.aevalTower
    ((IsScalarTower.toAlgHom A (P.obj (op Δ))
      (MvPolynomial (CellVariable d I Δ) (P.obj (op Δ)))).comp (P.map f.op).hom)
    (fun x => cellValue b Δ (f ≫ x.2.1) x.1)

/-- The structure map of an attachment acts on constants through the structure map of `P`. -/
lemma cellMap_C (b : CellBoundary P d I) {Δ Δ' : SimplexCategory}
    (f : Δ ⟶ Δ') (r : P.obj (op Δ')) :
    cellMap b f (MvPolynomial.C r) = MvPolynomial.C ((P.map f.op).hom r) := by
  simp [cellMap]

/-- The structure map along `f` of an attachment carries the generator `X x` to the cell value
along `f ≫ x.2.1` indexed by `x.1`. -/
lemma cellMap_X (b : CellBoundary P d I) {Δ Δ' : SimplexCategory}
    (f : Δ ⟶ Δ') (x : CellVariable d I Δ') :
    cellMap b f (MvPolynomial.X x) = cellValue b Δ (f ≫ x.2.1) x.1 := by
  simp [cellMap]

/-- The structure map along `f` of an attachment carries the cell value along `α` to the cell value
along `f ≫ α`. -/
lemma cellMap_value (b : CellBoundary P d I) {Δ Δ' : SimplexCategory}
    (f : Δ ⟶ Δ') (α : Δ' ⟶ ⦋d⦌) (i : I) :
    cellMap b f (cellValue b Δ' α i) = cellValue b Δ (f ≫ α) i := by
  classical
  by_cases h : Function.Surjective α.toOrderHom
  · simp only [cellValue, dite_eq_left h, cellMap_X]
  · simp only [cellValue, dite_eq_right h, cellMap_C,
      dite_eq_right (SimplexCategory.not_surjective_comp f α h), b.naturality]

/-- The structure map of an attachment along an identity is the identity. -/
lemma cellMap_id (b : CellBoundary P d I) (Δ : SimplexCategory) :
    cellMap b (𝟙 Δ) = AlgHom.id A _ := by
  classical
  apply AlgHom.toRingHom_injective
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [cellMap_C]
  · intro x
    simp [cellMap_X, cellValue, x.2.2]

/-- The structure map of an attachment along a composite is the composite of the structure maps. -/
lemma cellMap_comp (b : CellBoundary P d I) {Δ Δ' Δ'' : SimplexCategory}
    (f : Δ ⟶ Δ') (g : Δ' ⟶ Δ'') :
    cellMap b (f ≫ g) = (cellMap b f).comp (cellMap b g) := by
  apply AlgHom.toRingHom_injective
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [cellMap_C]
  · intro x
    simp [cellMap_X, cellMap_value, Category.assoc]

/-- The simplicial commutative `A`-algebra obtained from `P` by attaching `I` cells in degree `d`
along the boundary `b`. -/
noncomputable abbrev attachCells (b : CellBoundary P d I) :
    SimplicialObject (CommAlgCat.{max u v} A) where
  obj Δ := CommAlgCat.of A (MvPolynomial (CellVariable d I Δ.unop) (P.obj Δ))
  map f := CommAlgCat.ofHom (cellMap b f.unop)
  map_id Δ := CommAlgCat.hom_ext (cellMap_id b Δ.unop)
  map_comp f g := CommAlgCat.hom_ext (cellMap_comp b g.unop f.unop)

/-- The inclusion of `P` into an attachment, degreewise the inclusion of the coefficients. -/
noncomputable def attachCellsι (b : CellBoundary P d I) : P ⟶ attachCells b where
  app Δ := CommAlgCat.ofHom (IsScalarTower.toAlgHom A (P.obj Δ) _)
  naturality _ _ f := CommAlgCat.hom_ext (AlgHom.ext fun r => (cellMap_C b f.unop r).symm)

/-- The inclusion of `P` into an attachment sends `r` to the constant polynomial `C r`. -/
lemma attachCellsι_app (b : CellBoundary P d I) (Δ : SimplexCategoryᵒᵖ)
    (r : P.obj Δ) : (attachCellsι b).app Δ r = MvPolynomial.C r := rfl

/-- There are no cells in a degree below `d`, there being no surjection onto `⦋d⦌`. -/
lemma isEmpty_cellVariable {I : Type v} {Δ : SimplexCategory} (h : Δ.len < d) :
    IsEmpty (CellVariable d I Δ) := by
  refine ⟨fun x => ?_⟩
  have hc := Fintype.card_le_of_surjective _ x.2.2
  simp only [Fintype.card_fin] at hc
  omega

/-- A map of commutative `A`-algebras that is bijective on underlying types is an isomorphism. -/
theorem forgetReflectsIsomorphisms :
    (forget (CommAlgCat.{max u v} A)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (CommAlgCat.{max u v} A)).map f)
    let e : X ≃ₐ[A] Y := { f.hom, i.toEquiv with }
    exact (CommAlgCat.isoMk e).isIso_hom

attribute [local instance] forgetReflectsIsomorphisms

/-- Attaching cells in degree `d` changes nothing in the degrees below `d`. -/
lemma isIso_attachCellsι_app (b : CellBoundary P d I)
    (Δ : SimplexCategoryᵒᵖ) (h : Δ.unop.len < d) : IsIso ((attachCellsι b).app Δ) := by
  have := isEmpty_cellVariable (I := I) h
  apply (CategoryTheory.isIso_iff_of_reflects_iso _ (forget (CommAlgCat.{max u v} A))).mp
  rw [isIso_iff_bijective]
  exact (MvPolynomial.isEmptyAlgEquiv (P.obj Δ) (CellVariable d I Δ.unop)).symm.bijective

/-- The degree-`Δ` component of the map out of an attachment that extends `f` and sends the cell
indexed by `i` to `t i`. -/
noncomputable def cellDescApp (b : CellBoundary P d I)
    {Q : SimplicialObject (CommAlgCat.{max u v} A)} (f : P ⟶ Q)
    (t : I → Q.obj (op ⦋d⦌)) (Δ : SimplexCategoryᵒᵖ) :
    (attachCells b).obj Δ ⟶ Q.obj Δ :=
  CommAlgCat.ofHom (MvPolynomial.aevalTower (f.app Δ).hom
    (fun x => (Q.map x.2.1.op).hom (t x.1)))

/-- The map out of an attachment agrees with `f` on the constants. -/
lemma cellDescApp_C (b : CellBoundary P d I)
    {Q : SimplicialObject (CommAlgCat.{max u v} A)} (f : P ⟶ Q)
    (t : I → Q.obj (op ⦋d⦌)) (Δ : SimplexCategoryᵒᵖ) (r : P.obj Δ) :
    cellDescApp b f t Δ (MvPolynomial.C r) = f.app Δ r :=
  MvPolynomial.aevalTower_C _ _ _

/-- The map out of an attachment sends the generator of the cell indexed by `i` at a surjection
`α` to the image of `t i` under `α`. -/
lemma cellDescApp_X (b : CellBoundary P d I)
    {Q : SimplicialObject (CommAlgCat.{max u v} A)} (f : P ⟶ Q)
    (t : I → Q.obj (op ⦋d⦌)) (Δ : SimplexCategoryᵒᵖ) (x : CellVariable d I Δ.unop) :
    cellDescApp b f t Δ (MvPolynomial.X x) = Q.map x.2.1.op (t x.1) :=
  MvPolynomial.aevalTower_X _ _ _

/-- When `f` matches the images of the `t i` on the boundary, the map out of an attachment sends
the cell value along `α` indexed by `i` to the image of `t i` under `α`. -/
lemma cellDescApp_value (b : CellBoundary P d I)
    {Q : SimplicialObject (CommAlgCat.{max u v} A)} (f : P ⟶ Q)
    (t : I → Q.obj (op ⦋d⦌))
    (h : ∀ (Δ : SimplexCategory) (α : Δ ⟶ ⦋d⦌)
      (hα : ¬ Function.Surjective α.toOrderHom) (i : I),
      f.app (op Δ) (b.val Δ α hα i) = Q.map α.op (t i))
    (Δ : SimplexCategory) (α : Δ ⟶ ⦋d⦌) (i : I) :
    cellDescApp b f t (op Δ) (cellValue b Δ α i) = Q.map α.op (t i) := by
  classical
  unfold cellValue
  split_ifs with hα
  · exact cellDescApp_X b f t (op Δ) (i, ⟨α, hα⟩)
  · rw [cellDescApp_C, h]

/-- The map out of an attachment that extends `f : P ⟶ Q` and sends the cell indexed by `i` to
`t i`, prescribed on the boundary by the hypothesis `h`. -/
noncomputable def cellDesc (b : CellBoundary P d I)
    {Q : SimplicialObject (CommAlgCat.{max u v} A)} (f : P ⟶ Q)
    (t : I → Q.obj (op ⦋d⦌))
    (h : ∀ (Δ : SimplexCategory) (α : Δ ⟶ ⦋d⦌)
      (hα : ¬ Function.Surjective α.toOrderHom) (i : I),
      f.app (op Δ) (b.val Δ α hα i) = Q.map α.op (t i)) :
    attachCells b ⟶ Q where
  app := cellDescApp b f t
  naturality Δ Δ' g := by
    apply CommAlgCat.hom_ext
    apply AlgHom.toRingHom_injective
    apply MvPolynomial.ringHom_ext
    · intro r
      change cellDescApp b f t Δ' (cellMap b g.unop (MvPolynomial.C r)) =
        Q.map g (cellDescApp b f t Δ (MvPolynomial.C r))
      rw [cellMap_C, cellDescApp_C, cellDescApp_C]
      exact ConcreteCategory.congr_hom (f.naturality g) r
    · intro x
      change cellDescApp b f t Δ' (cellMap b g.unop (MvPolynomial.X x)) =
        Q.map g (cellDescApp b f t Δ (MvPolynomial.X x))
      rw [cellMap_X, cellDescApp_value b f t h, cellDescApp_X]
      simp

/-- The map out of an attachment restricts to `f` along the inclusion of `P`. -/
lemma attachCellsι_cellDesc (b : CellBoundary P d I)
    {Q : SimplicialObject (CommAlgCat.{max u v} A)} (f : P ⟶ Q)
    (t : I → Q.obj (op ⦋d⦌))
    (h : ∀ (Δ : SimplexCategory) (α : Δ ⟶ ⦋d⦌)
      (hα : ¬ Function.Surjective α.toOrderHom) (i : I),
      f.app (op Δ) (b.val Δ α hα i) = Q.map α.op (t i)) :
    attachCellsι b ≫ cellDesc b f t h = f :=
  NatTrans.ext <| funext fun Δ => CommAlgCat.hom_ext <| AlgHom.ext <| cellDescApp_C b f t Δ

/-- Given `I` elements of `Q` in degree `n + 1` and a map `P ⟶ Q` that is bijective in the degrees
at most `n`, the elements are the images of a cell boundary for `P` in degree `n + 1`. -/
lemma exists_cellBoundary_of_bijective {Q : SimplicialObject (CommAlgCat.{max u v} A)}
    (f : P ⟶ Q) (n : ℕ)
    (hf : ∀ k, k ≤ n → Function.Bijective (f.app (op ⦋k⦌)))
    (t : I → Q.obj (op ⦋n + 1⦌)) :
    ∃ b : CellBoundary P (n + 1) I,
      ∀ (Δ : SimplexCategory) (α : Δ ⟶ ⦋n + 1⦌)
        (hα : ¬ Function.Surjective α.toOrderHom) (i : I),
        f.app (op Δ) (b.val Δ α hα i) = Q.map α.op (t i) := by
  classical
  let F := Functor.whiskerRight f (forget (CommAlgCat.{max u v} A))
  have hF := SSet.boundary_postcomp_bijective F n hf
  choose g hg using fun i => hF.surjective
    (∂Δ[n + 1].ι ≫ SSet.yonedaEquiv.symm (t i))
  let b : CellBoundary P (n + 1) I :=
    { val := fun Δ α hα i => (g i).app (op Δ) ⟨SSet.stdSimplex.objEquiv.symm α, hα⟩
      naturality := by
        intro Δ Δ' φ α hα i
        exact (ConcreteCategory.congr_hom ((g i).naturality φ.op)
          ⟨SSet.stdSimplex.objEquiv.symm α, hα⟩).symm }
  exact ⟨b, fun Δ α hα i => ConcreteCategory.congr_hom (congr_app (hg i) (op Δ))
    ⟨SSet.stdSimplex.objEquiv.symm α, hα⟩⟩

/-- An isomorphism of commutative `A`-algebras over `B` is bijective. -/
lemma over_bijective_of_isIso {B : Type (max u v)} [CommRing B] [Algebra A B]
    {X Y : Over (CommAlgCat.of A B)} (f : X ⟶ Y) [IsIso f] :
    Function.Bijective f.left :=
  (isIso_iff_bijective ((Over.forget _ ⋙ forget (CommAlgCat.{max u v} A)).map f)).mp
    inferInstance

end CommAlgCat

end
