module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleCartesianComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.FppfHypercoveringLifts

/-!
# The descent datum of a cartesian sheaf on the small étale site of an fppf hypercovering

Let `a : U → X` be an fppf hypercovering of an algebraic space and `G` a cartesian sheaf on
`U_étale`. Its comparison isomorphism `α : d₁^* G_0 ≅ d₀^* G_0` over `U_1` satisfies the cocycle
condition over `U_2` and is the identity over the degenerate edges. Granting effective descent of
spaces-étale sheaves along fppf coverings, this file descends `α` along the fppf covering
`U_1 → U_0 ×_X U_0` and obtains a descent datum for `G_0` relative to `a_0 : U_0 → X`: the
compatibility of `α` over `U_1 ×_{U_0 ×_X U_0} U_1`, the cocycle condition over
`U_0 ×_X U_0 ×_X U_0` and the unit condition over the diagonal are all checked after a further
fppf covering, through the local lifts of edges and triangles of the hypercovering.

## Main definitions

* `AlgebraicGeometry.Space.EtaleComponent.descentPullback`: the chosen fibre product
  `U_0 ×_X U_0`.

## References

* [Stacks Project, Tag 0DH6](https://stacks.math.columbia.edu/tag/0DH6)
* [Stacks Project, Tag 0D7I](https://stacks.math.columbia.edu/tag/0D7I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Pseudofunctor
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open scoped Simplicial

universe u

namespace AlgebraicGeometry.Space.EtaleComponent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : SimplicialObject.Augmented (AlgebraicSpaces B S hS)}

/-! ### The degeneracy `U_0 → U_1` -/

variable (A) in
/-- The degeneracy `s₀ : U_0 → U_1`. -/
abbrev degen₀ : A.left.obj (op ⦋0⦌) ⟶ A.left.obj (op ⦋1⦌) :=
  A.left.map (SimplexCategory.σ 0 : ⦋1⦌ ⟶ ⦋0⦌).op

/-- The degeneracy `s₀ : U_0 → U_1` is a section of both faces `U_1 → U_0`. -/
theorem degen₀_face₁ (i : Fin 2) : degen₀ A ≫ face₁ A i = 𝟙 _ := by
  rw [← A.left.map_comp, ← op_comp, Subsingleton.elim (vertex₁ i ≫ _) (𝟙 ⦋0⦌), op_id,
    A.left.map_id]

/-- A face of an edge `U_2 → U_1` is a vertex `U_2 → U_0`. -/
theorem map_edge₂_comp_face₁ (j : Fin 3) (i : Fin 2) (k : Fin 3)
    (h : vertex₁ i ≫ edge₂ j = vertex₂ k) :
    A.left.map (edge₂ j).op ≫ face₁ A i = A.left.map (vertex₂ k).op := by
  rw [← A.left.map_comp, ← op_comp, h]

/-- If a triangle has an edge `σ ≫ edge₂ j` factoring as `c ≫ k` and `y` is a face of `k` that
is a vertex of the triangle, then `c ≫ y` is that vertex of `σ`. -/
private theorem comp_eq_vertex_of_edge {W W' : AlgebraicSpaces B S hS}
    {σ : W ⟶ A.left.obj (op ⦋2⦌)} {c : W ⟶ W'} {k : W' ⟶ A.left.obj (op ⦋1⦌)}
    {y : W' ⟶ A.left.obj (op ⦋0⦌)} {j : Fin 3} {i : Fin 2} {m : Fin 3}
    (h : vertex₁ i ≫ edge₂ j = vertex₂ m) (hσ : σ ≫ A.left.map (edge₂ j).op = c ≫ k)
    (hk : k ≫ face₁ A i = y) : c ≫ y = σ ≫ A.left.map (vertex₂ m).op := by
  rw [← map_edge₂_comp_face₁ j i m h, ← Category.assoc, hσ, Category.assoc, hk]

/-! ### Rigidity of the comparison isomorphism -/

section Rigidity

variable (hyp : IsFppfHypercovering A) (hdesc : EffectiveFppfDescent B S hS)
  (G : Sheaf (situation A).totalTopology (Type (u + 1)))
  (hG : SimplicialSiteSituation.IsCartesianSheaf (situation A) G)

/-- The comparison isomorphism pulled back along a triangle whose edge `d₀` is degenerate is
the identity, up to the equality of the two vertices of that edge. -/
theorem pullHom_cartesianComparison_of_degenerate_edge {W : AlgebraicSpaces B S hS}
    (σ : W ⟶ A.left.obj (op ⦋2⦌)) (y : W ⟶ A.left.obj (op ⦋0⦌))
    (hσ : σ ≫ A.left.map (edge₂ 0).op = y ≫ degen₀ A)
    (h₁ : y = σ ≫ A.left.map (vertex₂ 1).op) (h₂ : y = σ ≫ A.left.map (vertex₂ 2).op) :
    pullHom (F := spacesEtalePseudofunctor B S hS) (cartesianComparison G hG)
      (σ ≫ A.left.map (edge₂ 0).op) (σ ≫ A.left.map (vertex₂ 1).op)
      (σ ≫ A.left.map (vertex₂ 2).op)
      (by rw [Category.assoc,
        map_edge₂_comp_face₁ (A := A) 0 1 1 SimplexCategory.delta_one_comp_delta_zero])
      (by rw [Category.assoc,
        map_edge₂_comp_face₁ (A := A) 0 0 2 SimplexCategory.delta_zero_comp_delta_zero]) =
      eqToHom (congrArg (fun t : W ⟶ A.left.obj (op ⦋0⦌) =>
        ((spacesEtalePseudofunctor B S hS).map t.op.toLoc).toFunctor.obj (compF G ⦋0⦌))
        (h₁.symm.trans h₂)) := by
  have hd₁ : (y ≫ degen₀ A) ≫ face₁ A 1 = σ ≫ A.left.map (vertex₂ 1).op := by
    rw [Category.assoc, degen₀_face₁ (A := A) 1, Category.comp_id, h₁]
  have hd₀ : (y ≫ degen₀ A) ≫ face₁ A 0 = σ ≫ A.left.map (vertex₂ 2).op := by
    rw [Category.assoc, degen₀_face₁ (A := A) 0, Category.comp_id, h₂]
  have hu₁ : y ≫ A.left.map (𝟙 ⦋0⦌).op = σ ≫ A.left.map (vertex₂ 1).op := by
    rw [op_id, A.left.map_id, Category.comp_id, h₁]
  have hu₂ : y ≫ A.left.map (𝟙 ⦋0⦌).op = σ ≫ A.left.map (vertex₂ 2).op := by
    rw [op_id, A.left.map_id, Category.comp_id, h₂]
  rw [pullHom_congr_left _ hσ _ _ _ _ hd₁ hd₀,
    ← pullHom_pullHom (cartesianComparison G hG) (degen₀ A) (A.left.map (𝟙 ⦋0⦌).op)
      (A.left.map (𝟙 ⦋0⦌).op) y _ _
      (hgf₁ := (degen₀_face₁ (A := A) 1).trans (by rw [op_id, A.left.map_id]))
      (hgf₂ := (degen₀_face₁ (A := A) 0).trans (by rw [op_id, A.left.map_id]))
      (hg'f₁ := hu₁) (hg'f₂ := hu₂),
    pullHom_cartesianComparison_degenerate,
    pullHom_id_eq_eqToHom _ _ _ (h₁.symm.trans h₂)]

include hyp hdesc in
/-- **Rigidity of the comparison isomorphism**: two morphisms to `U_1` with the same vertices
pull the comparison isomorphism back to the same morphism. -/
theorem pullHom_cartesianComparison_eq {W : AlgebraicSpaces B S hS}
    (k₁ k₂ : W ⟶ A.left.obj (op ⦋1⦌)) (y₁ y₂ : W ⟶ A.left.obj (op ⦋0⦌))
    (h₁₁ : k₁ ≫ face₁ A 1 = y₁) (h₁₀ : k₁ ≫ face₁ A 0 = y₂)
    (h₂₁ : k₂ ≫ face₁ A 1 = y₁) (h₂₀ : k₂ ≫ face₁ A 0 = y₂) :
    pullHom (F := spacesEtalePseudofunctor B S hS) (cartesianComparison G hG) k₁ y₁ y₂ h₁₁ h₁₀ =
      pullHom (F := spacesEtalePseudofunctor B S hS) (cartesianComparison G hG) k₂ y₁ y₂
        h₂₁ h₂₀ := by
  obtain ⟨W', c, σ, hc, hσ₂, hσ₁, hσ₀⟩ := hyp.exists_triangle k₁ k₂ (y₂ ≫ degen₀ A)
    (h₁₁.trans h₂₁.symm)
    (by rw [Category.assoc]; exact h₁₀.trans ((Category.comp_id _).symm.trans
      (congrArg (y₂ ≫ ·) (degen₀_face₁ (A := A) 1).symm)))
    (by rw [Category.assoc]; exact h₂₀.trans ((Category.comp_id _).symm.trans
      (congrArg (y₂ ≫ ·) (degen₀_face₁ (A := A) 0).symm)))
  have e₂₁ := map_edge₂_comp_face₁ (A := A) 2 1 0 SimplexCategory.delta_one_comp_delta_two
  have e₂₀ := map_edge₂_comp_face₁ (A := A) 2 0 1 SimplexCategory.delta_zero_comp_delta_two
  have e₁₁ := map_edge₂_comp_face₁ (A := A) 1 1 0 SimplexCategory.delta_one_comp_delta_one
  have e₁₀ := map_edge₂_comp_face₁ (A := A) 1 0 2 SimplexCategory.delta_zero_comp_delta_one
  have hσ₂' : σ ≫ A.left.map (edge₂ 2).op = c ≫ k₁ := hσ₂
  have hσ₁' : σ ≫ A.left.map (edge₂ 1).op = c ≫ k₂ := hσ₁
  have hσ₀' : σ ≫ A.left.map (edge₂ 0).op = (c ≫ y₂) ≫ degen₀ A :=
    hσ₀.trans (Category.assoc _ _ _).symm
  have hv₀ := comp_eq_vertex_of_edge SimplexCategory.delta_one_comp_delta_two hσ₂' h₁₁
  have hv₁ := comp_eq_vertex_of_edge SimplexCategory.delta_zero_comp_delta_two hσ₂' h₁₀
  have hv₂ := comp_eq_vertex_of_edge SimplexCategory.delta_zero_comp_delta_one hσ₁' h₂₀
  have hcoc := cartesianComparison_cocycle_pullHom G hG σ
  have t₂ : pullHom (F := spacesEtalePseudofunctor B S hS) (cartesianComparison G hG)
      (σ ≫ A.left.map (edge₂ 2).op) (σ ≫ A.left.map (vertex₂ 0).op)
      (σ ≫ A.left.map (vertex₂ 1).op)
      (by rw [Category.assoc, e₂₁]) (by rw [Category.assoc, e₂₀]) =
      pullHom (pullHom (F := spacesEtalePseudofunctor B S hS) (cartesianComparison G hG) k₁ y₁ y₂
        h₁₁ h₁₀) c (σ ≫ A.left.map (vertex₂ 0).op) (σ ≫ A.left.map (vertex₂ 1).op) hv₀ hv₁ := by
    rw [pullHom_pullHom]
    exact pullHom_congr_left _ hσ₂' _ _ _ _ _ _
  have t₁ : pullHom (F := spacesEtalePseudofunctor B S hS) (cartesianComparison G hG)
      (σ ≫ A.left.map (edge₂ 1).op) (σ ≫ A.left.map (vertex₂ 0).op)
      (σ ≫ A.left.map (vertex₂ 2).op)
      (by rw [Category.assoc, e₁₁]) (by rw [Category.assoc, e₁₀]) =
      pullHom (pullHom (F := spacesEtalePseudofunctor B S hS) (cartesianComparison G hG) k₂ y₁ y₂
        h₂₁ h₂₀) c (σ ≫ A.left.map (vertex₂ 0).op) (σ ≫ A.left.map (vertex₂ 2).op) hv₀ hv₂ := by
    rw [pullHom_pullHom]
    exact pullHom_congr_left _ hσ₁' _ _ _ _ _ _
  rw [t₂, t₁, pullHom_cartesianComparison_of_degenerate_edge G hG σ (c ≫ y₂) hσ₀' hv₁ hv₂,
    pullHom_comp_eqToHom _ _ _ (hv₁.symm.trans hv₂) _ _ hv₂] at hcoc
  exact pullHom_injective c _ _ hv₀ hv₂ (fun a b h => hdesc.map_injective hc h) hcoc

end Rigidity

/-! ### The fibre product `U_0 ×_X U_0` and the edge morphism -/

variable (A) in
/-- The chosen fibre product `U_0 ×_X U_0`. -/
def descentPullback : ChosenPullback (augF A ⦋0⦌) (augF A ⦋0⦌) where
  pullback := pullback (augF A ⦋0⦌) (augF A ⦋0⦌)
  p₁ := pullback.fst _ _
  p₂ := pullback.snd _ _
  condition := pullback.condition
  isLimit := pullbackIsPullback _ _

variable (A) in
/-- The morphism `U_1 → U_0 ×_X U_0` whose components are the two faces. -/
def edgeMap : A.left.obj (op ⦋1⦌) ⟶ (descentPullback A).pullback :=
  pullback.lift (face₁ A 1) (face₁ A 0) (by rw [map_comp_augF, map_comp_augF])

/-- The first component of the edge morphism is the face `d₁ : U_1 → U_0`. -/
theorem edgeMap_p₁ : edgeMap A ≫ (descentPullback A).p₁ = face₁ A 1 := pullback.lift_fst _ _ _

/-- The second component of the edge morphism is the face `d₀ : U_1 → U_0`. -/
theorem edgeMap_p₂ : edgeMap A ≫ (descentPullback A).p₂ = face₁ A 0 := pullback.lift_snd _ _ _

/-- A morphism to `U_1` followed by the edge morphism factors through a morphism to
`U_0 ×_X U_0` once its two faces do. -/
theorem comp_edgeMap_eq_comp_lift {W W' : AlgebraicSpaces B S hS}
    (e : W ⟶ A.left.obj (op ⦋1⦌)) (c : W ⟶ W') (a b : W' ⟶ A.left.obj (op ⦋0⦌))
    (w : a ≫ augF A ⦋0⦌ = b ≫ augF A ⦋0⦌)
    (ha : e ≫ face₁ A 1 = c ≫ a) (hb : e ≫ face₁ A 0 = c ≫ b) :
    e ≫ edgeMap A = c ≫ (descentPullback A).isPullback.lift a b w := by
  apply (descentPullback A).isPullback.hom_ext
  · rw [Category.assoc, Category.assoc, edgeMap_p₁, IsPullback.lift_fst, ha]
  · rw [Category.assoc, Category.assoc, edgeMap_p₂, IsPullback.lift_snd, hb]

/-- For an fppf hypercovering, the edge morphism `U_1 → U_0 ×_X U_0` is an fppf covering. -/
theorem fppfSurjective_edgeMap (hyp : IsFppfHypercovering A) :
    fppfSurjective B S hS (edgeMap A) :=
  hyp.map_one

variable (A) in
/-- The chosen fibre product of the edge morphism with itself. -/
def edgePullback : ChosenPullback (edgeMap A) (edgeMap A) where
  pullback := pullback (edgeMap A) (edgeMap A)
  p₁ := pullback.fst _ _
  p₂ := pullback.snd _ _
  condition := pullback.condition
  isLimit := pullbackIsPullback _ _

variable (A) in
/-- The fibre product `(U_0 ×_X U_0) ×_{U_0} (U_0 ×_X U_0)`. -/
def descentPullbackPair : ChosenPullback (descentPullback A).p₂ (descentPullback A).p₁ where
  pullback := pullback (descentPullback A).p₂ (descentPullback A).p₁
  p₁ := pullback.fst _ _
  p₂ := pullback.snd _ _
  condition := pullback.condition
  isLimit := pullbackIsPullback _ _

/-- The outer projections of `(U_0 ×_X U_0) ×_{U_0} (U_0 ×_X U_0)` to `U_0` agree after
composing with `a_0 : U_0 → X`. -/
theorem descentPullbackPair_w :
    ((descentPullbackPair A).p₁ ≫ (descentPullback A).p₁) ≫ augF A ⦋0⦌ =
      ((descentPullbackPair A).p₂ ≫ (descentPullback A).p₂) ≫ augF A ⦋0⦌ := by
  rw [Category.assoc, Category.assoc, (descentPullback A).condition, ← Category.assoc,
    (descentPullbackPair A).condition, Category.assoc, (descentPullback A).condition]

variable (A) in
/-- The chosen threefold fibre product `U_0 ×_X U_0 ×_X U_0`. -/
def descentPullback₃ :
    ChosenPullback₃ (descentPullback A) (descentPullback A) (descentPullback A) where
  chosenPullback := descentPullbackPair A
  p := (descentPullbackPair A).p₁ ≫ (descentPullback A).p
  p₁ := (descentPullbackPair A).p₁ ≫ (descentPullback A).p₁
  p₃ := (descentPullbackPair A).p₂ ≫ (descentPullback A).p₂
  l :=
    { f := (descentPullback A).isPullback.lift _ _ descentPullbackPair_w
      f_p₁ := IsPullback.lift_fst _ _ _ _
      f_p₂ := IsPullback.lift_snd _ _ _ _
      f_p := by
        change _ ≫ (descentPullback A).p₁ ≫ augF A ⦋0⦌ = _
        rw [← Category.assoc, IsPullback.lift_fst]
        rfl }
  hp₁ := rfl
  hp₃ := rfl

/-! ### Descending the comparison isomorphism along `U_1 → U_0 ×_X U_0` -/

section Descend

variable (hyp : IsFppfHypercovering A) (hdesc : EffectiveFppfDescent B S hS)
  (G : Sheaf (situation A).totalTopology (Type (u + 1)))
  (hG : SimplicialSiteSituation.IsCartesianSheaf (situation A) G)

/-- The comparison isomorphism, transported to a morphism between the inverse images along the
edge morphism of the two inverse images of `G_0` to `U_0 ×_X U_0`. -/
def transportedComparison :
    ((spacesEtalePseudofunctor B S hS).map (edgeMap A).op.toLoc).toFunctor.obj
        (((spacesEtalePseudofunctor B S hS).map (descentPullback A).p₁.op.toLoc).toFunctor.obj
          (compF G ⦋0⦌)) ⟶
      ((spacesEtalePseudofunctor B S hS).map (edgeMap A).op.toLoc).toFunctor.obj
        (((spacesEtalePseudofunctor B S hS).map (descentPullback A).p₂.op.toLoc).toFunctor.obj
          (compF G ⦋0⦌)) :=
  ((spacesEtalePseudofunctor B S hS).mapComp' (descentPullback A).p₁.op.toLoc
      (edgeMap A).op.toLoc (face₁ A 1).op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, edgeMap_p₁])).inv.toNatTrans.app _ ≫
    cartesianComparison G hG ≫
    ((spacesEtalePseudofunctor B S hS).mapComp' (descentPullback A).p₂.op.toLoc
      (edgeMap A).op.toLoc (face₁ A 0).op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, edgeMap_p₂])).hom.toNatTrans.app _

include hyp hdesc in
/-- **The comparison isomorphism descends along `U_1 → U_0 ×_X U_0`.** -/
theorem exists_descendedComparison :
    ∃ φ : ((spacesEtalePseudofunctor B S hS).map (descentPullback A).p₁.op.toLoc).toFunctor.obj
          (compF G ⦋0⦌) ⟶
        ((spacesEtalePseudofunctor B S hS).map (descentPullback A).p₂.op.toLoc).toFunctor.obj
          (compF G ⦋0⦌),
      (spacesEtaleInverseImage B S hS (edgeMap A)).map φ = transportedComparison G hG := by
  refine hdesc.exists_map_eq (fppfSurjective_edgeMap hyp) (edgePullback A) _
    (descentSquareApp_comm_of_pullHom_eq _ _ ?_)
  have hq₁ : (edgePullback A).p₁ ≫ edgeMap A = (edgePullback A).p := (edgePullback A).hp₁
  have hq₂ : (edgePullback A).p₂ ≫ edgeMap A = (edgePullback A).p := (edgePullback A).hp₂
  dsimp only [transportedComparison]
  rw [pullHom_transport _ _ _ _ _ edgeMap_p₁ edgeMap_p₂ _ _ _ hq₁ _ _ rfl rfl,
    pullHom_transport _ _ _ _ _ edgeMap_p₁ edgeMap_p₂ _ _ _ hq₂ _ _ rfl rfl,
    pullHom_cartesianComparison_eq hyp hdesc G hG (edgePullback A).p₁ (edgePullback A).p₂]

/-- **The descended comparison**: the morphism over `U_0 ×_X U_0` whose pullback to `U_1` is the
comparison isomorphism. -/
def descendedComparison :
    ((spacesEtalePseudofunctor B S hS).map (descentPullback A).p₁.op.toLoc).toFunctor.obj
        (compF G ⦋0⦌) ⟶
      ((spacesEtalePseudofunctor B S hS).map (descentPullback A).p₂.op.toLoc).toFunctor.obj
        (compF G ⦋0⦌) :=
  (exists_descendedComparison hyp hdesc G hG).choose

/-- The pullback of the descended comparison along the edge morphism `U_1 → U_0 ×_X U_0` is
the comparison isomorphism. -/
theorem pullHom_descendedComparison :
    pullHom (F := spacesEtalePseudofunctor B S hS) (descendedComparison hyp hdesc G hG)
        (edgeMap A) (face₁ A 1) (face₁ A 0) edgeMap_p₁ edgeMap_p₂ =
      cartesianComparison G hG :=
  pullHom_eq_of_map_eq _ _ _ _ _ edgeMap_p₁ edgeMap_p₂ _ _
    (exists_descendedComparison hyp hdesc G hG).choose_spec

/-- **The descended comparison over an edge**: pulled back along a morphism to `U_0 ×_X U_0`
which lifts to `U_1`, the descended comparison is the comparison isomorphism pulled back along
the lift. -/
theorem pullHom_descendedComparison_of_lift {W : AlgebraicSpaces B S hS}
    (k : W ⟶ A.left.obj (op ⦋1⦌)) (r : W ⟶ (descentPullback A).pullback)
    (hk : k ≫ edgeMap A = r) (z₁ z₂ : W ⟶ A.left.obj (op ⦋0⦌))
    (h₁ : r ≫ (descentPullback A).p₁ = z₁) (h₂ : r ≫ (descentPullback A).p₂ = z₂)
    (h₁' : k ≫ face₁ A 1 = z₁) (h₂' : k ≫ face₁ A 0 = z₂) :
    pullHom (F := spacesEtalePseudofunctor B S hS) (descendedComparison hyp hdesc G hG)
        r z₁ z₂ h₁ h₂ =
      pullHom (F := spacesEtalePseudofunctor B S hS) (cartesianComparison G hG) k z₁ z₂
        h₁' h₂' := by
  rw [← pullHom_descendedComparison hyp hdesc G hG, pullHom_pullHom]
  exact pullHom_congr_left _ hk.symm _ _ _ _ _ _

include hyp hdesc in
/-- The unit condition of the descended comparison: it is the identity over the diagonal. -/
theorem pullHom_descendedComparison_diagonal :
    pullHom (F := spacesEtalePseudofunctor B S hS) (descendedComparison hyp hdesc G hG)
        ((descentPullback A).isPullback.lift (𝟙 _) (𝟙 _) rfl) (𝟙 _) (𝟙 _)
        (IsPullback.lift_fst _ _ _ _) (IsPullback.lift_snd _ _ _ _) = 𝟙 _ := by
  have hk : degen₀ A ≫ edgeMap A = (descentPullback A).isPullback.lift (𝟙 _) (𝟙 _) rfl := by
    apply (descentPullback A).isPullback.hom_ext
    · rw [Category.assoc, edgeMap_p₁, degen₀_face₁, IsPullback.lift_fst]
    · rw [Category.assoc, edgeMap_p₂, degen₀_face₁, IsPullback.lift_snd]
  rw [pullHom_descendedComparison_of_lift hyp hdesc G hG (degen₀ A) _ hk _ _ _ _
      (degen₀_face₁ (A := A) 1) (degen₀_face₁ (A := A) 0),
    ← cartesianComparison_degenerate_pullHom G hG (𝟙 _)]
  exact pullHom_congr_left _ (Category.id_comp _).symm _ _ _ _ _ _

include hyp hdesc in
/-- **The cocycle condition of the descended comparison**, over `U_0 ×_X U_0 ×_X U_0`. -/
theorem descendedComparison_cocycle (x₁ x₂ x₃ : (descentPullback₃ A).pullback ⟶ A.left.obj (op ⦋0⦌))
    (w₁₂ : x₁ ≫ augF A ⦋0⦌ = x₂ ≫ augF A ⦋0⦌) (w₂₃ : x₂ ≫ augF A ⦋0⦌ = x₃ ≫ augF A ⦋0⦌)
    (w₁₃ : x₁ ≫ augF A ⦋0⦌ = x₃ ≫ augF A ⦋0⦌) :
    pullHom (F := spacesEtalePseudofunctor B S hS) (descendedComparison hyp hdesc G hG)
        ((descentPullback A).isPullback.lift x₁ x₂ w₁₂) x₁ x₂
        (IsPullback.lift_fst _ _ _ _) (IsPullback.lift_snd _ _ _ _) ≫
      pullHom (F := spacesEtalePseudofunctor B S hS) (descendedComparison hyp hdesc G hG)
        ((descentPullback A).isPullback.lift x₂ x₃ w₂₃) x₂ x₃
        (IsPullback.lift_fst _ _ _ _) (IsPullback.lift_snd _ _ _ _) =
      pullHom (F := spacesEtalePseudofunctor B S hS) (descendedComparison hyp hdesc G hG)
        ((descentPullback A).isPullback.lift x₁ x₃ w₁₃) x₁ x₃
        (IsPullback.lift_fst _ _ _ _) (IsPullback.lift_snd _ _ _ _) := by
  obtain ⟨T₁, c₁, t₀₁, hc₁, ht₀₁₁, ht₀₁₀⟩ := hyp.exists_edge x₁ x₂ w₁₂
  obtain ⟨T₂, c₂, t₁₂, hc₂, ht₁₂₁, ht₁₂₀⟩ := hyp.exists_edge (c₁ ≫ x₂) (c₁ ≫ x₃)
    (by rw [Category.assoc, Category.assoc]; exact congrArg (c₁ ≫ ·) w₂₃)
  obtain ⟨T₃, c₃, t₀₂, hc₃, ht₀₂₁, ht₀₂₀⟩ := hyp.exists_edge (c₂ ≫ c₁ ≫ x₁) (c₂ ≫ c₁ ≫ x₃)
    (by simp only [Category.assoc]; exact congrArg (fun t => c₂ ≫ c₁ ≫ t) w₁₃)
  obtain ⟨W, c₄, σ, hc₄, hσ₂, hσ₁, hσ₀⟩ := hyp.exists_triangle (c₃ ≫ c₂ ≫ t₀₁) t₀₂ (c₃ ≫ t₁₂)
    (by simp only [Category.assoc]; rw [ht₀₁₁, ht₀₂₁])
    (by simp only [Category.assoc]; rw [ht₀₁₀, ht₁₂₁])
    (by simp only [Category.assoc]; rw [ht₀₂₀, ht₁₂₀])
  have hc : fppfSurjective B S hS (c₄ ≫ c₃ ≫ c₂ ≫ c₁) :=
    fppfSurjective_comp hc₄ (fppfSurjective_comp hc₃ (fppfSurjective_comp hc₂ hc₁))
  have e₂₁ := map_edge₂_comp_face₁ (A := A) 2 1 0 SimplexCategory.delta_one_comp_delta_two
  have e₂₀ := map_edge₂_comp_face₁ (A := A) 2 0 1 SimplexCategory.delta_zero_comp_delta_two
  have e₁₁ := map_edge₂_comp_face₁ (A := A) 1 1 0 SimplexCategory.delta_one_comp_delta_one
  have e₁₀ := map_edge₂_comp_face₁ (A := A) 1 0 2 SimplexCategory.delta_zero_comp_delta_one
  have e₀₁ := map_edge₂_comp_face₁ (A := A) 0 1 1 SimplexCategory.delta_one_comp_delta_zero
  have e₀₀ := map_edge₂_comp_face₁ (A := A) 0 0 2 SimplexCategory.delta_zero_comp_delta_zero
  have hσ₂' : σ ≫ A.left.map (edge₂ 2).op = (c₄ ≫ c₃ ≫ c₂) ≫ t₀₁ :=
    hσ₂.trans (by simp only [Category.assoc])
  have hσ₁' : σ ≫ A.left.map (edge₂ 1).op = c₄ ≫ t₀₂ := hσ₁
  have ht₀₁₁' : t₀₁ ≫ face₁ A 1 = c₁ ≫ x₁ := ht₀₁₁
  have ht₀₁₀' : t₀₁ ≫ face₁ A 0 = c₁ ≫ x₂ := ht₀₁₀
  have ht₀₂₀' : t₀₂ ≫ face₁ A 0 = c₃ ≫ c₂ ≫ c₁ ≫ x₃ := ht₀₂₀
  have hz₀ : (c₄ ≫ c₃ ≫ c₂ ≫ c₁) ≫ x₁ = σ ≫ A.left.map (vertex₂ 0).op := by
    simpa only [Category.assoc] using
      comp_eq_vertex_of_edge SimplexCategory.delta_one_comp_delta_two hσ₂' ht₀₁₁'
  have hz₁ : (c₄ ≫ c₃ ≫ c₂ ≫ c₁) ≫ x₂ = σ ≫ A.left.map (vertex₂ 1).op := by
    simpa only [Category.assoc] using
      comp_eq_vertex_of_edge SimplexCategory.delta_zero_comp_delta_two hσ₂' ht₀₁₀'
  have hz₂ : (c₄ ≫ c₃ ≫ c₂ ≫ c₁) ≫ x₃ = σ ≫ A.left.map (vertex₂ 2).op := by
    simpa only [Category.assoc] using
      comp_eq_vertex_of_edge SimplexCategory.delta_zero_comp_delta_one hσ₁' ht₀₂₀'
  have hk₂ := comp_edgeMap_eq_comp_lift (σ ≫ A.left.map (edge₂ 2).op) (c₄ ≫ c₃ ≫ c₂ ≫ c₁)
    x₁ x₂ w₁₂ (by rw [hz₀, Category.assoc, e₂₁]) (by rw [hz₁, Category.assoc, e₂₀])
  have hk₀ := comp_edgeMap_eq_comp_lift (σ ≫ A.left.map (edge₂ 0).op) (c₄ ≫ c₃ ≫ c₂ ≫ c₁)
    x₂ x₃ w₂₃ (by rw [hz₁, Category.assoc, e₀₁]) (by rw [hz₂, Category.assoc, e₀₀])
  have hk₁ := comp_edgeMap_eq_comp_lift (σ ≫ A.left.map (edge₂ 1).op) (c₄ ≫ c₃ ≫ c₂ ≫ c₁)
    x₁ x₃ w₁₃ (by rw [hz₀, Category.assoc, e₁₁]) (by rw [hz₂, Category.assoc, e₁₀])
  apply pullHom_injective (c₄ ≫ c₃ ≫ c₂ ≫ c₁) (σ ≫ A.left.map (vertex₂ 0).op)
    (σ ≫ A.left.map (vertex₂ 2).op) hz₀ hz₂ (fun a b h => hdesc.map_injective hc h)
  rw [pullHom_comp (gf₂ := σ ≫ A.left.map (vertex₂ 1).op)
      (hgf₂ := hz₁),
    pullHom_pullHom, pullHom_pullHom, pullHom_pullHom,
    pullHom_descendedComparison_of_lift hyp hdesc G hG _ _ hk₂ _ _ _ _
      (by rw [Category.assoc, e₂₁]) (by rw [Category.assoc, e₂₀]),
    pullHom_descendedComparison_of_lift hyp hdesc G hG _ _ hk₀ _ _ _ _
      (by rw [Category.assoc, e₀₁]) (by rw [Category.assoc, e₀₀]),
    pullHom_descendedComparison_of_lift hyp hdesc G hG _ _ hk₁ _ _ _ _
      (by rw [Category.assoc, e₁₁]) (by rw [Category.assoc, e₁₀])]
  exact cartesianComparison_cocycle_pullHom G hG σ

/-- **The descent datum of a cartesian sheaf** relative to `a_0 : U_0 → X`, over the chosen fibre
products: the degree-zero component with the descended comparison. -/
def cartesianDescentDatum' :
    (spacesEtalePseudofunctor B S hS).DescentData' (f := fun _ : Unit => augF A ⦋0⦌)
      (fun _ _ => descentPullback A) (fun _ _ _ => descentPullback₃ A) where
  obj _ := compF G ⦋0⦌
  hom _ _ := descendedComparison hyp hdesc G hG
  pullHom'_hom_self _ := pullHom_descendedComparison_diagonal hyp hdesc G hG
  pullHom'_hom_comp _ _ _ := descendedComparison_cocycle hyp hdesc G hG _ _ _
    ((descentPullback₃ A).w₁.trans (descentPullback₃ A).w₂.symm)
    ((descentPullback₃ A).w₂.trans (descentPullback₃ A).w₃.symm)
    ((descentPullback₃ A).w₁.trans (descentPullback₃ A).w₃.symm)

/-- **The descent datum of a cartesian sheaf** relative to `a_0 : U_0 → X`. -/
def cartesianDescentDatum :
    (spacesEtalePseudofunctor B S hS).DescentData (fun _ : Unit => augF A ⦋0⦌) :=
  (cartesianDescentDatum' hyp hdesc G hG).descentData

/-- The object of the descent datum of a cartesian sheaf is its degree-zero component `G_0`. -/
theorem cartesianDescentDatum_obj (i : Unit) :
    (cartesianDescentDatum hyp hdesc G hG).obj i = compF G ⦋0⦌ := rfl

/-- Over `U_1`, the transition of the descent datum of a cartesian sheaf is its comparison
isomorphism. -/
theorem cartesianDescentDatum_hom_edge :
    (cartesianDescentDatum hyp hdesc G hG).hom (augF A ⦋1⦌) (i₁ := ()) (i₂ := ())
        (face₁ A 1) (face₁ A 0) (map_comp_augF _) (map_comp_augF _) =
      cartesianComparison G hG := by
  have hl : (descentPullback A).isPullback.lift (face₁ A 1) (face₁ A 0)
      (by rw [map_comp_augF, map_comp_augF]) = edgeMap A :=
    (descentPullback A).isPullback.hom_ext (by rw [IsPullback.lift_fst, edgeMap_p₁])
      (by rw [IsPullback.lift_snd, edgeMap_p₂])
  rw [← pullHom_descendedComparison hyp hdesc G hG]
  exact pullHom_congr_left (descendedComparison hyp hdesc G hG) hl _ _
    (IsPullback.lift_fst _ _ _ _) (IsPullback.lift_snd _ _ _ _) edgeMap_p₁ edgeMap_p₂

end Descend

end AlgebraicGeometry.Space.EtaleComponent
