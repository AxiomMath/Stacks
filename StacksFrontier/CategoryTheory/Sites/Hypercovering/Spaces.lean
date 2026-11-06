module

public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Coskeletal
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Basic

/-!
# Hypercoverings of a topological space

Let `X` be a topological space, regarded as a site through the pretopology of its opens. A
hypercovering of `X` is a simplicial semi-representable object over the whole space, that is a
simplicial object of `FormalCoproduct (Over (⊤ : Opens X))`, so each of its degrees is a family of
opens of `X`. This file proves the three covering equations the source records for such an object:
the degree-zero opens cover the whole space, the opens attached to two vertices meet in the union
of the opens attached to the edges with those two vertices as faces, and, in every higher degree,
a compatible family of `n + 3` faces intersects in the union of the opens whose faces are exactly
that family.

## Main results

* `iSup_eq_top_of_isHypercovering`: Tag 01H2 — the degree-zero opens have supremum the whole
  space.
* `inf_eq_iSup_edges`: Tag 01H3 — two degree-zero opens intersect in the union of the degree-one
  opens with the prescribed faces.
* `intersection_eq_union_of_isHypercovering`: Tag 01H4 — the multiple-intersection covering
  equation in every degree at least one.

## Implementation notes

The simplicial set of indices and its face maps are the index types and index maps of the
simplicial formal coproduct; a face map on indices is therefore the `f` component of the
corresponding morphism of formal coproducts. Unions and intersections of opens are the suprema and
infima of the complete lattice `Opens X`.

All three equations are the covering clause of `IsHypercovering` read in this pretopology. Tag
01H2 is the degree-zero clause itself: the target of that covering morphism is the terminal formal
coproduct, whose single component is the whole space, so the clause already says that every point
is covered. The other two proofs must identify the relevant matching object. For Tag 01H3 that
object is reached by a cone on the degree-one matching diagram whose point is the one-member
family consisting of the intersection of the two vertex opens, lifted through the pointwise right
Kan extension computing `(cosk₀ K)₁`. For Tag 01H4 the matching object is constructed outright,
as the family indexed by the compatible systems of faces, and `matchingObjectIso` identifies it
with `(cosk_{n+1} K)_{n+2}`.
In both cases the comparison with the face maps of `K` rests on
`unit_comp_cosk_map_comp_counit`, the triangle identity of the coskeleton adjunction in the form
that recovers a face map of `K` from its image in the coskeleton.

The source's degree `n ≥ 1` in Tag 01H4 is written as `n + 1`, so that the positivity hypothesis
is built into the indexing and no transport between finite index types is needed.

## References

* [Stacks Project, Tag 01H2](https://stacks.math.columbia.edu/tag/01H2)
* [Stacks Project, Tag 01H3](https://stacks.math.columbia.edu/tag/01H3)
* [Stacks Project, Tag 01H4](https://stacks.math.columbia.edu/tag/01H4)
-/

@[expose] public section

universe w u

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite Simplicial
  TopologicalSpace
open scoped SimplexCategory.Truncated CategoryTheory.SimplicialObject.Truncated

namespace Stacks.CategoryTheory.Hypercovering

namespace SpaceMatching

/-! ### The triangle identity of the coskeleton adjunction -/

/-- The composite of the unit of the coskeleton adjunction with the image in the coskeleton of a
simplicial operator landing in a truncated degree, followed by the counit, is that operator's
action on the original simplicial object. -/
theorem unit_comp_cosk_map_comp_counit {D : Type u} [Category.{w} D] (K : SimplicialObject D)
    (m : ℕ)
    [∀ F : SimplicialObject.Truncated D m,
      (SimplexCategory.Truncated.inclusion m).op.HasPointwiseRightKanExtension F]
    {k l : ℕ} (hk : k ≤ m) (φ : SimplexCategory.mk k ⟶ SimplexCategory.mk l) :
    ((SimplicialObject.coskAdj m).unit.app K).app (op (SimplexCategory.mk l)) ≫
        ((SimplicialObject.cosk m).obj K).map φ.op ≫
        ((SimplicialObject.coskAdj m).counit.app
          ((SimplicialObject.truncation m).obj K)).app (op ⟨SimplexCategory.mk k, hk⟩) =
      K.map φ.op := by
  let cu : ((SimplicialObject.cosk m).obj K).obj (op (SimplexCategory.mk k)) ⟶
      K.obj (op (SimplexCategory.mk k)) :=
    ((SimplicialObject.coskAdj m).counit.app ((SimplicialObject.truncation m).obj K)).app
      (op ⟨SimplexCategory.mk k, hk⟩)
  show ((SimplicialObject.coskAdj m).unit.app K).app (op (SimplexCategory.mk l)) ≫
    ((SimplicialObject.cosk m).obj K).map φ.op ≫ cu = K.map φ.op
  have ht := congrArg
    (fun t : (SimplicialObject.truncation m).obj K ⟶ (SimplicialObject.truncation m).obj K ↦
      t.app (op ⟨SimplexCategory.mk k, hk⟩))
    ((SimplicialObject.coskAdj (C := D) m).left_triangle_components K)
  dsimp only [NatTrans.comp_app, NatTrans.id_app] at ht
  have h0 : ((SimplicialObject.coskAdj m).unit.app K).app (op (SimplexCategory.mk k)) ≫ cu =
      𝟙 (K.obj (op (SimplexCategory.mk k))) := ht
  have hnat : K.map φ.op ≫
        ((SimplicialObject.coskAdj m).unit.app K).app (op (SimplexCategory.mk k)) =
      ((SimplicialObject.coskAdj m).unit.app K).app (op (SimplexCategory.mk l)) ≫
        ((SimplicialObject.cosk m).obj K).map φ.op :=
    ((SimplicialObject.coskAdj m).unit.app K).naturality φ.op
  rw [← Category.assoc, ← hnat, Category.assoc, h0, Category.comp_id]

/-- Over a covering morphism of semi-representable objects, every point of a target component lies
in a source component mapping to it. -/
theorem exists_component_of_isCoveringOver (X : Type u) [TopologicalSpace X]
    {A B : FormalCoproduct.{w} (Over (⊤ : Opens X))} (f : A ⟶ B)
    (hf : IsCoveringOver (Opens.pretopology X) f)
    (k : B.I) (x : X) (hx : x ∈ (B.obj k).left) :
    ∃ j : A.I, f.f j = k ∧ x ∈ (A.obj j).left := by
  obtain ⟨_, _, ⟨j⟩, hxV⟩ := hf k x hx
  exact ⟨j.1, j.2, hxV⟩

/-- A morphism of semi-representable objects maps the open of an index into the open of its
image. -/
private theorem left_le_of_f_eq {X : Type u} [TopologicalSpace X]
    {A B : FormalCoproduct.{w} (Over (⊤ : Opens X))} (f : A ⟶ B) (i : A.I) {k : B.I}
    (h : f.f i = k) : (A.obj i).left ≤ (B.obj k).left :=
  h ▸ (f.φ i).left.le

/-! ### Tag 01H3: the matching object in degree one -/

section Edges

variable {X : Type u} [TopologicalSpace X]

/-- The semi-representable objects over the whole space, in which a hypercovering of `X` lives. -/
private abbrev FC (X : Type u) [TopologicalSpace X] :=
  FormalCoproduct.{w} (Over (⊤ : Opens X))

private abbrev L := (SimplexCategory.Truncated.inclusion 0).op

private abbrev zeroT : (SimplexCategory.Truncated 0)ᵒᵖ :=
  op (⟨⦋0⦌, by decide⟩ : SimplexCategory.Truncated 0)

private instance : Subsingleton (SimplexCategory.Truncated 0) := by
  constructor
  rintro ⟨⟨m⟩, hm⟩ ⟨⟨n⟩, hn⟩
  obtain rfl : m = 0 := Nat.eq_zero_of_le_zero hm
  obtain rfl : n = 0 := Nat.eq_zero_of_le_zero hn
  rfl

private instance (a b : SimplexCategory.Truncated 0) : Subsingleton (a ⟶ b) := by
  constructor
  intro f g
  apply SimplexCategory.Truncated.Hom.ext
  apply OrderHom.ext
  funext x
  have hb : b.1.len = 0 := Nat.eq_zero_of_le_zero b.2
  cases b with
  | mk Δ hΔ =>
    cases Δ with
    | mk k =>
      obtain rfl : k = 0 := Nat.eq_zero_of_le_zero hΔ
      apply Fin.ext
      omega

/-- The open on which two chosen vertices meet, regarded as an object over the whole space. -/
private noncomputable def meetOpen (K : SimplicialObject (FC X))
    (i₀ i₁ : (K.obj (op ⦋0⦌)).I) : Over (⊤ : Opens X) :=
  Over.mk (homOfLE (le_top : ((K.obj (op ⦋0⦌)).obj i₀).left ⊓
    ((K.obj (op ⦋0⦌)).obj i₁).left ≤ ⊤))

/-- The vertex of an edge selected by an index of `Fin 2`. -/
private def vertex {α : Type*} (i₀ i₁ : α) (a : Fin 2) : α :=
  if a = 1 then i₀ else i₁

/-- Every arrow from degree one to the zero-truncated category selects one of the two vertices,
and the intersection of the two vertex opens is contained in the selected one. -/
private noncomputable def leg (K : SimplicialObject (FC X))
    (i₀ i₁ : (K.obj (op ⦋0⦌)).I)
    (g : StructuredArrow (op ⦋1⦌) L) :
    ((FormalCoproduct.incl (Over (⊤ : Opens X))).obj (meetOpen K i₀ i₁)) ⟶
      ((SimplicialObject.truncation 0).obj K).obj g.right := by
  let a : Fin 2 := g.hom.unop.toOrderHom 0
  rcases g with ⟨_, ⟨⟨⟨n⟩, hn⟩⟩, f⟩
  obtain rfl : n = 0 := Nat.eq_zero_of_le_zero hn
  exact FormalCoproduct.Hom.fromIncl (vertex i₀ i₁ a) (Over.homMk (homOfLE (by
    change ((K.obj (op ⦋0⦌)).obj i₀).left ⊓
      ((K.obj (op ⦋0⦌)).obj i₁).left ≤ ((K.obj (op ⦋0⦌)).obj (vertex i₀ i₁ a)).left
    dsimp [vertex]
    split
    · exact inf_le_left
    · exact inf_le_right)))

/-- The cone on the degree-one matching diagram whose point is the one-member family consisting
of the intersection of the two vertex opens. -/
private noncomputable def matchingCone (K : SimplicialObject (FC X))
    (i₀ i₁ : (K.obj (op ⦋0⦌)).I) :
    Cone (StructuredArrow.proj (op ⦋1⦌) L ⋙ (SimplicialObject.truncation 0).obj K) where
  pt := (FormalCoproduct.incl (Over (⊤ : Opens X))).obj (meetOpen K i₀ i₁)
  π :=
    { app := leg K i₀ i₁
      naturality := by
        intro g g' φ
        have hright : g.right = g'.right := Subsingleton.elim _ _
        have hφ : φ.right = eqToHom hright := Subsingleton.elim _ _
        obtain rfl : g = g' := StructuredArrow.obj_ext g g' hright (by
          rw [← hφ]
          exact StructuredArrow.w φ)
        obtain rfl : φ = 𝟙 g := StructuredArrow.hom_ext φ (𝟙 g) (Subsingleton.elim _ _)
        simp }

/-- The zeroth coskeleton, presented as a right extension along the zero-truncation. -/
private noncomputable def matchingExtension (K : SimplicialObject (FC X)) :
    RightExtension L ((SimplicialObject.truncation 0).obj K) :=
  RightExtension.mk _ ((SimplicialObject.coskAdj 0).counit.app
    ((SimplicialObject.truncation 0).obj K))

private noncomputable def matchingPointwise (K : SimplicialObject (FC X)) :
    (matchingExtension K).IsPointwiseRightKanExtensionAt (op ⦋1⦌) := by
  letI : (matchingExtension K).left.IsRightKanExtension (matchingExtension K).hom := by
    change ((L.ran).obj ((SimplicialObject.truncation 0).obj K)).IsRightKanExtension
      ((L.ranAdjunction (FC X)).counit.app ((SimplicialObject.truncation 0).obj K))
    rw [Functor.ranAdjunction_counit]
    infer_instance
  exact (Functor.isPointwiseRightKanExtensionOfIsRightKanExtension
    (matchingExtension K).left (matchingExtension K).hom) (op ⦋1⦌)

/-- The morphism to the degree-one matching object induced by `matchingCone`. -/
private noncomputable def matchingLift (K : SimplicialObject (FC X))
    (i₀ i₁ : (K.obj (op ⦋0⦌)).I) :
    ((FormalCoproduct.incl (Over (⊤ : Opens X))).obj (meetOpen K i₀ i₁)) ⟶
      (((SimplicialObject.cosk 0).obj K).obj (op ⦋1⦌)) :=
  (matchingPointwise K).lift (matchingCone K i₀ i₁)

/-- The `d`-th face inclusion, as an object of the index category of the matching diagram. -/
private def faceArrow (d : Fin 2) : StructuredArrow (op ⦋1⦌) L :=
  StructuredArrow.mk (Quiver.Hom.op (SimplexCategory.δ d) : op ⦋1⦌ ⟶ L.obj zeroT)

private theorem leg_face_f (K : SimplicialObject (FC X))
    (i₀ i₁ : (K.obj (op ⦋0⦌)).I) (d : Fin 2) :
    (leg K i₀ i₁ (faceArrow d)).f PUnit.unit = if d = 0 then i₀ else i₁ := by
  fin_cases d <;> simp [leg, faceArrow, StructuredArrow.mk, vertex, SimplexCategory.δ,
    FormalCoproduct.Hom.fromIncl] <;>
    dsimp [StructuredArrow.hom, Comma.hom, SimplexCategory.Hom.toOrderHom,
      SimplexCategory.Hom.mk, Fin.succAboveOrderEmb] <;>
    first
    | rfl
    | (intro h; exact absurd rfl h)
    | (intro h; exact absurd h (by decide))

private theorem matchingLift_face (K : SimplicialObject (FC X))
    (i₀ i₁ : (K.obj (op ⦋0⦌)).I) (d : Fin 2) :
    matchingLift K i₀ i₁ ≫
      (((SimplicialObject.cosk 0).obj K).map (SimplexCategory.δ d).op) ≫
      ((SimplicialObject.coskAdj 0).counit.app
        ((SimplicialObject.truncation 0).obj K)).app zeroT =
      leg K i₀ i₁ (faceArrow d) := by
  convert (matchingPointwise K).fac (matchingCone K i₀ i₁) (faceArrow d) using 1
  rfl

/-- The component of the degree-one matching object selected by the lift contains the
intersection of the two vertex opens, and every edge over it has the prescribed faces. -/
private theorem matching_index (K : SimplicialObject (FC X))
    (i₀ i₁ : (K.obj (op ⦋0⦌)).I) :
    let e := ((SimplicialObject.coskAdj 0).unit.app K).app (op ⦋1⦌)
    let M := ((SimplicialObject.cosk 0).obj K).obj (op ⦋1⦌)
    ∃ j : M.I, (meetOpen K i₀ i₁).left ≤ (M.obj j).left ∧
      ∀ i : (K.obj (op ⦋1⦌)).I, e.f i = j →
        (K.δ (0 : Fin 2)).f i = i₀ ∧ (K.δ (1 : Fin 2)).f i = i₁ := by
  let l := matchingLift K i₀ i₁
  refine ⟨l.f PUnit.unit, (l.φ PUnit.unit).left.le, fun i hi ↦ ?_⟩
  have face_index (d : Fin 2) : (K.δ d).f i = if d = 0 then i₀ else i₁ := by
    let p := (((SimplicialObject.cosk 0).obj K).map (SimplexCategory.δ d).op) ≫
      ((SimplicialObject.coskAdj 0).counit.app
        ((SimplicialObject.truncation 0).obj K)).app zeroT
    have hu : p.f (((SimplicialObject.coskAdj 0).unit.app K).app (op ⦋1⦌) |>.f i) =
        (K.δ d).f i :=
      congrArg (fun f : (K.obj (op ⦋1⦌)) ⟶ (K.obj (op ⦋0⦌)) ↦ f.f i)
        (unit_comp_cosk_map_comp_counit K 0 le_rfl (SimplexCategory.δ d))
    have hl : p.f (l.f PUnit.unit) = (leg K i₀ i₁ (faceArrow d)).f PUnit.unit :=
      congrArg (fun f : ((FormalCoproduct.incl (Over (⊤ : Opens X))).obj
        (meetOpen K i₀ i₁)) ⟶ (K.obj (op ⦋0⦌)) ↦ f.f PUnit.unit)
        (matchingLift_face K i₀ i₁ d)
    exact ((hu.symm.trans (congrArg p.f hi)).trans hl).trans (leg_face_f K i₀ i₁ d)
  exact ⟨by simpa using face_index 0, by simpa using face_index 1⟩

/-- One half of Tag 01H3: the intersection of two vertex opens is covered by the edge opens with
those two vertices as faces. -/
private theorem inf_le_iSup_edges (K : SimplicialObject (FC X))
    (hK : IsHypercovering (Opens.pretopology X) K)
    (i₀ i₁ : (K.obj (op ⦋0⦌)).I) :
    ((K.obj (op ⦋0⦌)).obj i₀).left ⊓ ((K.obj (op ⦋0⦌)).obj i₁).left ≤
      ⨆ i : { i : (K.obj (op ⦋1⦌)).I //
          (K.δ (0 : Fin 2)).f i = i₀ ∧ (K.δ (1 : Fin 2)).f i = i₁ },
        ((K.obj (op ⦋1⦌)).obj i.1).left := by
  intro x hx
  obtain ⟨j, hj, hfaces⟩ := matching_index K i₀ i₁
  obtain ⟨i, hij, hxU⟩ := exists_component_of_isCoveringOver X _ (hK.2 0) j x (hj hx)
  exact Opens.mem_iSup.mpr ⟨⟨i, hfaces i hij⟩, hxU⟩

end Edges

/-- Any cone on the degree-`n + 2` matching diagram of an `(n + 1)`-truncated simplicial object
satisfies the simplicial identities relating its legs at the `n + 3` face inclusions. -/
private lemma coneFaces_compat {D : Type u} [Category.{w} D] (n : ℕ)
    (U : SimplicialObject.Truncated D (n + 1))
    (s : Cone (StructuredArrow.proj (op ⦋n + 2⦌)
      (SimplexCategory.Truncated.inclusion (n + 1)).op ⋙ U)) :
    ∀ i j : Fin (n + 2), i ≤ j →
      s.π.app (StructuredArrow.mk (Y := op ⦋n + 1⦌ₙ₊₁) (SimplexCategory.δ i.castSucc).op) ≫
          U.map (SimplexCategory.Truncated.δ (n + 1) j (by trunc) (by trunc)).op =
        s.π.app (StructuredArrow.mk (Y := op ⦋n + 1⦌ₙ₊₁) (SimplexCategory.δ j.succ).op) ≫
          U.map (SimplexCategory.Truncated.δ (n + 1) i (by trunc) (by trunc)).op :=
  fun i j hij ↦
    (s.w (StructuredArrow.homMk
      (f := StructuredArrow.mk (Y := op ⦋n + 1⦌ₙ₊₁) (SimplexCategory.δ i.castSucc).op)
      (f' := StructuredArrow.mk (Y := op ⦋n⦌ₙ₊₁)
        (SimplexCategory.δ j ≫ SimplexCategory.δ i.castSucc).op)
      ((SimplexCategory.Truncated.δ (n + 1) j (by trunc) (by trunc)).op)
      (by simp))).trans
    (s.w (StructuredArrow.homMk
      (f := StructuredArrow.mk (Y := op ⦋n + 1⦌ₙ₊₁) (SimplexCategory.δ j.succ).op)
      (f' := StructuredArrow.mk (Y := op ⦋n⦌ₙ₊₁)
        (SimplexCategory.δ j ≫ SimplexCategory.δ i.castSucc).op)
      ((SimplexCategory.Truncated.δ (n + 1) i (by trunc) (by trunc)).op)
      (by simp [← op_comp, SimplexCategory.δ_comp_δ hij]))).symm

/-! ### Tag 01H4: the matching object in higher degrees -/

section HigherFaces

variable (X : Type u) [TopologicalSpace X]
  (K : SimplicialObject (FormalCoproduct.{w} (Over (⊤ : Opens X)))) (n : ℕ)

/-- The degree-`n + 2` matching object: the family indexed by the compatible systems of `n + 3`
degree-`n + 1` indices, with component the intersection of the corresponding opens. -/
private noncomputable def matchingObject : FormalCoproduct.{w} (Over (⊤ : Opens X)) where
  I := { i : (a : Fin (n + 3)) → (K.obj (op (SimplexCategory.mk (n + 1)))).I //
    ∀ (a b : Fin (n + 3)) (hab : a < b),
      (K.δ (b.pred (ne_of_gt (lt_of_le_of_lt (Fin.zero_le a) hab)))).f (i a) =
        (K.δ (a.castPred (ne_of_lt (lt_of_lt_of_le hab (Fin.le_last b))))).f (i b) }
  obj i := Over.mk (show (⨅ a, ((K.obj (op (SimplexCategory.mk (n + 1)))).obj (i.1 a)).left) ⟶
    (⊤ : Opens X) from homOfLE le_top)

/-- The `a`-th projection of the matching object. -/
private noncomputable def matchingFace (a : Fin (n + 3)) :
    matchingObject X K n ⟶ K.obj (op (SimplexCategory.mk (n + 1))) where
  f i := i.1 a
  φ i := Over.homMk (homOfLE (iInf_le _ a))

private lemma matchingFace_compat :
    ∀ a b : Fin (n + 2), a ≤ b →
      matchingFace X K n a.castSucc ≫ K.map (SimplexCategory.δ b).op =
        matchingFace X K n b.succ ≫ K.map (SimplexCategory.δ a).op :=
  fun a b hab ↦ FormalCoproduct.hom_ext
    (funext fun i ↦ i.2 a.castSucc b.succ (Fin.castSucc_lt_succ_iff.mpr hab)) fun _ ↦ rfl

private lemma matchingFace_universal
    (T : FormalCoproduct.{w} (Over (⊤ : Opens X)))
    (g : Fin (n + 3) → (T ⟶ K.obj (op (SimplexCategory.mk (n + 1)))))
    (hg : ∀ a b : Fin (n + 2), a ≤ b →
      g a.castSucc ≫ K.map (SimplexCategory.δ b).op =
        g b.succ ≫ K.map (SimplexCategory.δ a).op) :
    ∃! h : T ⟶ matchingObject X K n, ∀ a, h ≫ matchingFace X K n a = g a := by
  let f : T.I → (matchingObject X K n).I := fun t ↦ ⟨fun a ↦ (g a).f t, by
    intro a b hab
    obtain ⟨a', rfl⟩ : ∃ a', a = a'.castSucc :=
      ⟨a.castPred (Fin.ne_last_of_lt hab), (Fin.castSucc_castPred _ _).symm⟩
    obtain ⟨b', rfl⟩ : ∃ b', b = b'.succ :=
      ⟨b.pred (Fin.ne_of_gt ((Fin.zero_le _).trans_lt hab)), (Fin.succ_pred _ _).symm⟩
    exact congrFun (congrArg FormalCoproduct.Hom.f
      (hg a' b' (Fin.castSucc_lt_succ_iff.mp hab))) t⟩
  let h : T ⟶ matchingObject X K n :=
    { f := f
      φ := fun t ↦ Over.homMk (homOfLE (le_iInf fun a ↦ ((g a).φ t).left.le)) }
  exact ⟨h, fun a ↦ FormalCoproduct.hom_ext rfl fun _ ↦ rfl, fun h' hh' ↦
    FormalCoproduct.hom_ext (funext fun t ↦ Subtype.ext (funext fun a ↦
      congrFun (congrArg FormalCoproduct.Hom.f (hh' a)) t)) fun _ ↦ rfl⟩

/-- `matchingObject` with its face projections is a limit of the degree-`n + 2` matching
diagram. -/
private noncomputable def matchingLimitCone :
    LimitCone (StructuredArrow.proj (op ⦋n + 2⦌)
      (SimplexCategory.Truncated.inclusion (n + 1)).op ⋙
        (SimplicialObject.truncation (n + 1)).obj K) := by
  let U := (SimplicialObject.truncation (n + 1)).obj K
  have hπex :=
    (SimplicialObject.Truncated.existsUnique_cone_app_δ_eq_iff
      U (matchingObject X K n) (matchingFace X K n)).mpr (matchingFace_compat X K n)
  let π := Classical.choose hπex
  have hπ := (Classical.choose_spec hπex).1
  let s := Cone.mk (matchingObject X K n) π
  refine ⟨s, IsLimit.ofExistsUnique (fun t ↦ ?_)⟩
  let g : Fin (n + 3) → (t.pt ⟶ K.obj (op (SimplexCategory.mk (n + 1)))) := fun a ↦
    t.π.app (StructuredArrow.mk (Y := op ⦋n + 1⦌ₙ₊₁) (SimplexCategory.δ a).op)
  obtain ⟨h, hh, huh⟩ := matchingFace_universal X K n t.pt g (coneFaces_compat n U t)
  have hπg :=
    (SimplicialObject.Truncated.existsUnique_cone_app_δ_eq_iff U t.pt g).mpr
      (coneFaces_compat n U t)
  have hcone : (Functor.const _).map h ≫ π = t.π :=
    ((Classical.choose_spec hπg).2 _ (fun a ↦ by
      dsimp
      rw [hπ a]
      exact hh a)).trans ((Classical.choose_spec hπg).2 t.π (fun _ ↦ rfl)).symm
  refine ⟨h, fun j ↦ congrArg (fun q ↦ q.app j) hcone, fun h' hh' ↦ huh h' fun a ↦ ?_⟩
  rw [← hπ a]
  exact hh' _

private lemma matchingLimitCone_π_face (a : Fin (n + 3)) :
    (matchingLimitCone X K n).cone.π.app
        (StructuredArrow.mk (Y := op ⦋n + 1⦌ₙ₊₁) (SimplexCategory.δ a).op) =
      matchingFace X K n a := by
  let U := (SimplicialObject.truncation (n + 1)).obj K
  let hπex := (SimplicialObject.Truncated.existsUnique_cone_app_δ_eq_iff
    U (matchingObject X K n) (matchingFace X K n)).mpr (matchingFace_compat X K n)
  show (Classical.choose hπex).app _ = _
  exact (Classical.choose_spec hπex).1 a

/-- The comparison of `matchingObject` with the degree-`n + 2` term of the `(n + 1)`-st
coskeleton. -/
private noncomputable def matchingObjectIso :
    ((SimplicialObject.cosk (n + 1)).obj K).obj (op (SimplexCategory.mk (n + 2))) ≅
      matchingObject X K n := by
  let L := (SimplexCategory.Truncated.inclusion (n + 1)).op
  let U := (SimplicialObject.truncation (n + 1)).obj K
  have hE := Functor.isPointwiseRightKanExtensionOfIsRightKanExtension
    (L.rightKanExtension U) (L.rightKanExtensionCounit U)
  exact IsLimit.conePointUniqueUpToIso (hE (op ⦋n + 2⦌)) (matchingLimitCone X K n).isLimit

private lemma matchingObjectIso_hom_face (a : Fin (n + 3)) :
    (matchingObjectIso X K n).hom ≫ matchingFace X K n a =
      ((SimplicialObject.cosk (n + 1)).obj K).map (SimplexCategory.δ a).op ≫
        ((SimplexCategory.Truncated.inclusion (n + 1)).op.rightKanExtensionCounit
          ((SimplicialObject.truncation (n + 1)).obj K)).app (op ⦋n + 1⦌ₙ₊₁) := by
  rw [← matchingLimitCone_π_face X K n a]
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

/-- The canonical morphism from degree `n + 2` to `matchingObject`. -/
private noncomputable def toMatchingObject :
    K.obj (op (SimplexCategory.mk (n + 2))) ⟶ matchingObject X K n :=
  ((SimplicialObject.coskAdj (n + 1)).unit.app K).app (op (SimplexCategory.mk (n + 2))) ≫
    (matchingObjectIso X K n).hom

private lemma toMatchingObject_comp_face (a : Fin (n + 3)) :
    toMatchingObject X K n ≫ matchingFace X K n a = K.δ a := by
  rw [toMatchingObject, Category.assoc, matchingObjectIso_hom_face]
  exact unit_comp_cosk_map_comp_counit K (n + 1) le_rfl (SimplexCategory.δ a)

end HigherFaces

end SpaceMatching

open SpaceMatching

/-- **Stacks Project, Tag 01H2.** In a hypercovering of a topological space, the opens attached
to the degree-zero indices cover the whole space. -/
@[stacks 01H2]
theorem iSup_eq_top_of_isHypercovering {X : Type u} [TopologicalSpace X]
    (K : SimplicialObject (FormalCoproduct.{w} (Over (⊤ : Opens X))))
    (hK : IsHypercovering (Opens.pretopology X) K) :
    (⨆ i : (K.obj (Opposite.op ⦋0⦌)).I, ((K.obj (Opposite.op ⦋0⦌)).obj i).left) = ⊤ := by
  refine le_antisymm le_top fun x _ ↦ ?_
  let e := (FormalCoproduct.isTerminalIncl (Over.mk (𝟙 (⊤ : Opens X)))
    Over.mkIdTerminal).uniqueUpToIso terminalIsTerminal
  have hx : x ∈ ((⊤_ (FormalCoproduct.{w} (Over (⊤ : Opens X)))).obj
      (e.hom.f PUnit.unit)).left := (e.hom.φ PUnit.unit).left.le trivial
  obtain ⟨j, -, hxj⟩ := exists_component_of_isCoveringOver X
    (terminal.from (K.obj (op ⦋0⦌))) hK.1 _ x hx
  exact Opens.mem_iSup.mpr ⟨j, hxj⟩

/-- **Stacks Project, Tag 01H3.** In a hypercovering of a topological space, the intersection of
the opens attached to two vertices is the union of the opens attached to the edges whose zeroth
and first faces are those vertices. -/
@[stacks 01H3]
theorem inf_eq_iSup_edges {X : Type u} [TopologicalSpace X]
    (K : SimplicialObject (FormalCoproduct.{w} (Over (⊤ : Opens X))))
    (hK : IsHypercovering (Opens.pretopology X) K)
    (i₀ i₁ : (K.obj (Opposite.op ⦋0⦌)).I) :
    ((K.obj (Opposite.op ⦋0⦌)).obj i₀).left ⊓
        ((K.obj (Opposite.op ⦋0⦌)).obj i₁).left =
      ⨆ i : { i : (K.obj (Opposite.op ⦋1⦌)).I //
          (K.δ (0 : Fin 2)).f i = i₀ ∧ (K.δ (1 : Fin 2)).f i = i₁ },
        ((K.obj (Opposite.op ⦋1⦌)).obj i.1).left := by
  refine le_antisymm (inf_le_iSup_edges K hK i₀ i₁) (iSup_le fun i ↦ le_inf ?_ ?_)
  · exact left_le_of_f_eq (K.δ (0 : Fin 2)) i.1 i.2.1
  · exact left_le_of_f_eq (K.δ (1 : Fin 2)) i.1 i.2.2

/-- **Stacks Project, Tag 01H4.** In a hypercovering of a topological space, the intersection of
a compatible family of `n + 3` degree-`n + 1` opens is the union of the degree-`n + 2` opens whose
faces are the prescribed family. This is the source's equation in every degree at least one. -/
@[stacks 01H4]
theorem intersection_eq_union_of_isHypercovering
    (X : Type u) [TopologicalSpace X]
    (K : SimplicialObject (FormalCoproduct.{w} (Over (⊤ : Opens X))))
    (hK : IsHypercovering (Opens.pretopology X) K)
    (n : ℕ)
    (i : (a : Fin (n + 3)) → (K.obj (Opposite.op (SimplexCategory.mk (n + 1)))).I)
    (hi : ∀ (a b : Fin (n + 3)) (hab : a < b),
      (K.δ (b.pred (ne_of_gt (lt_of_le_of_lt (Fin.zero_le a) hab)))).f (i a) =
        (K.δ (a.castPred (ne_of_lt (lt_of_lt_of_le hab (Fin.le_last b))))).f (i b)) :
    (⨅ a, ((K.obj (Opposite.op (SimplexCategory.mk (n + 1)))).obj (i a)).left) =
      ⨆ j : { j : (K.obj (Opposite.op (SimplexCategory.mk (n + 2)))).I //
        ∀ a, (K.δ a).f j = i a },
        ((K.obj (Opposite.op (SimplexCategory.mk (n + 2)))).obj j.1).left := by
  classical
  let M := matchingObject X K n
  let m : M.I := ⟨i, hi⟩
  let e := matchingObjectIso X K n
  let q := ((SimplicialObject.coskAdj (n + 1)).unit.app K).app
    (Opposite.op (SimplexCategory.mk (n + 2)))
  apply le_antisymm
  · intro x hx
    obtain ⟨j, hjk, hxj⟩ := exists_component_of_isCoveringOver X q
      (hK.2 (n + 1)) (e.inv.f m) x ((e.inv.φ m).left.le hx)
    have hindex : (toMatchingObject X K n).f j = m := by
      show e.hom.f (q.f j) = m
      rw [hjk]
      exact congrFun (congrArg FormalCoproduct.Hom.f e.inv_hom_id) m
    have hfaces : ∀ a, (K.δ a).f j = i a := fun a ↦
      (congrFun (congrArg FormalCoproduct.Hom.f
        (toMatchingObject_comp_face X K n a)) j).symm.trans
          (congrArg (fun t : M.I ↦ t.1 a) hindex)
    exact Opens.mem_iSup.mpr ⟨⟨j, hfaces⟩, hxj⟩
  · exact iSup_le fun j ↦ le_iInf fun a ↦ left_le_of_f_eq (K.δ a) j.1 (j.2 a)

end Stacks.CategoryTheory.Hypercovering

end
