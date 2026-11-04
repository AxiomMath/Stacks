module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalExtension.Components
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleSeparablyClosed
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The connected components of a product of smooth projective schemes

Let `k` be algebraically closed and let `X`, `Y` be smooth projective schemes over `k`. For
connected components `X_c` of `X` and `Y_d` of `Y` the open and closed subscheme
`pr₁⁻¹(X_c) ∩ pr₂⁻¹(Y_d)` of `X × Y` is the product `X_c ×_k Y_d`, which is irreducible, both
factors being irreducible over an algebraically closed field. Hence the connected components of
`X × Y` are exactly these products, and `E ↦ (pr₁(E), pr₂(E))` identifies the components of
`X × Y` with pairs of components of `X` and `Y`. This is how the Künneth formula for the
extension of a classical Weil cohomology theory to all smooth projective schemes reduces to the
Künneth formula on smooth projective varieties.

## Main results

* `Stacks.WeilCohomology.SmoothProjectiveScheme.compOpens_prod`: the component `E` of
  `X × Y` is `pr₁⁻¹(X_{pr₁ E}) ∩ pr₂⁻¹(Y_{pr₂ E})`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.bijective_compMap_fst_snd`: components of
  `X × Y` are pairs of components.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.isPullback_resIdx_fst_snd`: the component of
  `X × Y` of index `E` is the fibre product of the components of `X` and `Y` it projects to.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.WeilCohomology.SmoothProjectiveScheme

variable {k : Type u} [Field k] [IsAlgClosed k] (X Y : (SmoothProjectiveScheme k).FullSubcategory)

/-- The open subset `pr₁⁻¹(X_c) ∩ pr₂⁻¹(Y_d)` of `X × Y`. -/
def prodPiece (c : Components X) (d : Components Y) : Set (prod X Y).obj.left :=
  (fst X Y).hom.left ⁻¹' (compOpens X c : Set X.obj.left) ∩
    (snd X Y).hom.left ⁻¹' (compOpens Y d : Set Y.obj.left)

/-- The open immersion `X_c ×_k Y_d ⟶ X ×_k Y`. -/
def prodPieceMap (c : Components X) (d : Components Y) :
    Limits.pullback (comp X c).obj.hom (comp Y d).obj.hom ⟶ (prod X Y).obj.left :=
  Limits.pullback.map (comp X c).obj.hom (comp Y d).obj.hom X.obj.hom Y.obj.hom (compOpens X c).ι
    (compOpens Y d).ι (𝟙 _) (Category.comp_id _) (Category.comp_id _)

/-- The morphism `X_c ×_k Y_d ⟶ X ×_k Y` is an open immersion. -/
instance isOpenImmersion_prodPieceMap (c : Components X) (d : Components Y) :
    IsOpenImmersion (prodPieceMap X Y c d) :=
  MorphismProperty.pullbackMap (P := @IsOpenImmersion) (inferInstance : IsOpenImmersion _)
    (inferInstance : IsOpenImmersion _) rfl rfl

omit [IsAlgClosed k] in
/-- The range of `X_c ×_k Y_d ⟶ X ×_k Y` is `pr₁⁻¹(X_c) ∩ pr₂⁻¹(Y_d)`. -/
theorem range_prodPieceMap (c : Components X) (d : Components Y) :
    Set.range (prodPieceMap X Y c d) = prodPiece X Y c d := by
  have h := Scheme.Pullback.range_map (f := (comp X c).obj.hom) (g := (comp Y d).obj.hom)
    X.obj.hom Y.obj.hom (compOpens X c).ι (compOpens Y d).ι (𝟙 _) (Category.comp_id _)
    (Category.comp_id _)
  rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι] at h
  exact h

/-- `X_c ×_k Y_d` is irreducible over the algebraically closed field `k`. -/
instance irreducibleSpace_pullback_comp (c : Components X) (d : Components Y) :
    IrreducibleSpace (Limits.pullback (comp X c).obj.hom (comp Y d).obj.hom : Scheme.{u}) := by
  have : IsIntegral (comp X c).obj.left := (comp X c).2.1.toIsVariety.toIsIntegral
  have : IsIntegral (comp Y d).obj.left := (comp Y d).2.1.toIsVariety.toIsIntegral
  have : GeometricallyIrreducible (comp X c).obj.hom :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k _ _
  have : GeometricallyIrreducible (comp Y d).obj.hom :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k _ _
  infer_instance

/-- The subset `pr₁⁻¹(X_c) ∩ pr₂⁻¹(Y_d)` of `X × Y` is preconnected. -/
theorem isPreconnected_prodPiece (c : Components X) (d : Components Y) :
    _root_.IsPreconnected (prodPiece X Y c d) := by
  rw [← range_prodPieceMap, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).2.isPreconnected.image _
    (prodPieceMap X Y c d).continuous.continuousOn

/-- The subset `pr₁⁻¹(X_c) ∩ pr₂⁻¹(Y_d)` of `X × Y` is nonempty. -/
theorem nonempty_prodPiece (c : Components X) (d : Components Y) :
    (prodPiece X Y c d).Nonempty := by
  rw [← range_prodPieceMap]
  exact Set.range_nonempty _

omit [IsAlgClosed k] in
/-- The map on connected components induced by `f : X ⟶ Y` sends the component of `x` to the
component of `f x`. -/
theorem compMap_mk {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (x : X.obj.left) :
    compMap f (_root_.ConnectedComponents.mk x) = _root_.ConnectedComponents.mk (f.hom.left x) :=
  Continuous.connectedComponentsMap_mk _ x

/-- **The component `E` of `X × Y` is `pr₁⁻¹(X_{pr₁ E}) ∩ pr₂⁻¹(Y_{pr₂ E})`.** -/
theorem compOpens_prod (E : Components (prod X Y)) :
    (compOpens (prod X Y) E : Set (prod X Y).obj.left) =
      prodPiece X Y (compMap (fst X Y) E) (compMap (snd X Y) E) := by
  obtain ⟨z, rfl⟩ := _root_.ConnectedComponents.surjective_coe E
  have hE : (compOpens (prod X Y) (_root_.ConnectedComponents.mk z) : Set (prod X Y).obj.left) =
      connectedComponent z := by
    rw [Scheme.coe_connectedComponentOpens, connectedComponents_preimage_singleton]
  refine Set.Subset.antisymm (fun z' hz' ↦ ?_) ?_
  · have h : _root_.ConnectedComponents.mk z' = _root_.ConnectedComponents.mk z := hz'
    constructor <;> exact (compMap_mk _ z').symm.trans (congrArg _ h)
  · rw [hE]
    refine (isPreconnected_prodPiece X Y _ _).subset_connectedComponent ?_
    constructor <;> exact (compMap_mk _ z).symm

/-- **The components of `X × Y` are the pairs of components of `X` and `Y`.** -/
theorem bijective_compMap_fst_snd :
    Function.Bijective fun E : Components (prod X Y) ↦
      (compMap (fst X Y) E, compMap (snd X Y) E) := by
  refine ⟨fun E E' h ↦ ?_, fun ⟨c, d⟩ ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := _root_.ConnectedComponents.surjective_coe E
    simp only [Prod.mk.injEq] at h
    have hz : z ∈ (compOpens (prod X Y) E' : Set (prod X Y).obj.left) := by
      rw [compOpens_prod, ← h.1, ← h.2, ← compOpens_prod]
      rfl
    exact hz
  · obtain ⟨z, hz⟩ := nonempty_prodPiece X Y c d
    refine ⟨_root_.ConnectedComponents.mk z, ?_⟩
    have h := (compOpens_prod X Y (_root_.ConnectedComponents.mk z)).subset
      (show z ∈ (compOpens (prod X Y) (_root_.ConnectedComponents.mk z) : Set _) from rfl)
    exact Prod.ext ((show _ = _ from h.1).symm.trans hz.1) ((show _ = _ from h.2).symm.trans hz.2)

/-- **The component of `X × Y` of index `E` is the fibre product of the components of `X` and
`Y` it projects to.** -/
theorem isPullback_resIdx_fst_snd (E : Idx (prod X Y)) :
    IsPullback (resIdx (fst X Y) E).hom.left (resIdx (snd X Y) E).hom.left
      (compAt X (idxMap (fst X Y) E)).obj.hom (compAt Y (idxMap (snd X Y) E)).obj.hom := by
  set c := idxEquiv X (idxMap (fst X Y) E)
  set d := idxEquiv Y (idxMap (snd X Y) E)
  have hrange : Set.range (compOpens (prod X Y) (idxEquiv _ E)).ι =
      Set.range (prodPieceMap X Y c d) := by
    rw [Scheme.Opens.range_ι, range_prodPieceMap, compOpens_prod, ← idxEquiv_idxMap,
      ← idxEquiv_idxMap]
  let φ := IsOpenImmersion.isoOfRangeEq _ _ hrange
  have : Mono (compOpens X c).ι := IsOpenImmersion.mono _
  have : Mono (compOpens Y d).ι := IsOpenImmersion.mono _
  have h1 : prodPieceMap X Y c d ≫ (fst X Y).hom.left =
      Limits.pullback.fst _ _ ≫ (compOpens X c).ι :=
    pullback.lift_fst _ _ _
  have h2 : prodPieceMap X Y c d ≫ (snd X Y).hom.left =
      Limits.pullback.snd _ _ ≫ (compOpens Y d).ι :=
    pullback.lift_snd _ _ _
  refine IsPullback.of_iso_pullback ⟨?_⟩ φ ?_ ?_
  · rw [comp_obj_hom, comp_obj_hom, ← Category.assoc, ← Category.assoc, resIdx_left_ι,
      resIdx_left_ι, Category.assoc, Category.assoc, Over.w (fst X Y).hom, Over.w (snd X Y).hom]
  · refine Mono.right_cancellation (f := (compOpens X c).ι) _ _ ?_
    rw [Category.assoc, ← h1, ← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac,
      resIdx_left_ι]
  · refine Mono.right_cancellation (f := (compOpens Y d).ι) _ _ ?_
    rw [Category.assoc, ← h2, ← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac,
      resIdx_left_ι]

end Stacks.WeilCohomology.SmoothProjectiveScheme

end
