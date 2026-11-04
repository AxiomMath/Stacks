module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectGlueCharts
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectGlueIso

/-!
# Zariski glueing for the comparison functor of Tag 0EXD

Let `p` be a prime and let `q ≫ b = e ≫ z` be a commutative square of schemes in characteristic
`p`, with comparison functor `G : 𝒮_X ⥤ 𝒮_Z ×_{𝒮_E} 𝒮_{X'}`.  This file proves the step "*another
Zariski glueing argument finishes the proof*" of [Stacks, Tag 0EXD] for an arbitrary such square:
an object `T` of the categorical fibre product which, over each member `V j` of an open cover of
`X`, is the image of a free module under the comparison functor of the restricted square, is in the
essential image of `G` — provided the restricted comparison functors are full and faithful over the
pairwise intersections and faithful over the triple ones.

## Main results

* `AlgebraicGeometry.mem_essImage_frobeniusColimitVectorBundlesComparison_of_cover`: the glueing.
* `AlgebraicGeometry.frobeniusColimitLocResHom_chart`: restricting the local isomorphism built from
  a chart and a local solution.

## Implementation notes

The overlap isomorphisms of the free charts are the preimages under the restricted comparison
functor over `V j ⊓ V k` of the comparisons of the two moved local solutions; their identity and
cocycle conditions follow from faithfulness by
`AlgebraicGeometry.frobeniusColimitFreeRes_localSolution`.  The module is glued by
`AlgebraicGeometry.exists_frobeniusColimitVectorBundle_glue`, which records the charts, and the
local isomorphisms between the restrictions of `G N` and of `T` are glued by
`AlgebraicGeometry.nonempty_iso_of_frobeniusColimitLocRestrict`, their agreement on overlaps being
`AlgebraicGeometry.frobeniusColimitLocResHom_chart` together with the compatibility of the charts.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime] {X X' Z E : Scheme.{u}}
  (b : X' ⟶ X) (z : Z ⟶ X) (q : E ⟶ X') (e : E ⟶ Z)
  (hX : IsInCharacteristic X p) (hX' : IsInCharacteristic X' p)
  (hZ : IsInCharacteristic Z p) (hE : IsInCharacteristic E p) (hw : q ≫ b = e ≫ z)

local notation "G[" U "]" => frobeniusColimitComparisonRestrict p b z q e hX hX' hZ hE hw U
local notation "L[" U "]" => frobeniusColimitLocRestrict p b z q e hX' hZ hE hw U
local notation "F[" U ", " n "]" =>
  frobeniusColimitFreeVectorBundle p (isInCharacteristic_toScheme hX U) n


/-- **Restricting the local isomorphism built from a chart and a local solution.** -/
theorem frobeniusColimitLocResHom_chart (T : CategoricalPullback
      (frobeniusColimitVectorBundlesPullback p e hE hZ)
      (frobeniusColimitVectorBundlesPullback p q hE hX'))
    (N : frobeniusColimitVectorBundles X p hX) {V W : X.Opens} (h : W ≤ V) {n : ℕ}
    (c : (frobeniusColimitVectorBundlesPullback p V.ι (isInCharacteristic_toScheme hX V) hX).obj N ≅
      F[V, n]) (β : G[V].obj F[V, n] ≅ L[V].obj T) :
    frobeniusColimitLocResHom p b z q e hX' hZ hE hw h
        ((frobeniusColimitLocRestrictIso p b z q e hX hX' hZ hE hw V N).hom ≫
          G[V].map c.hom ≫ β.hom) =
      (frobeniusColimitLocRestrictIso p b z q e hX hX' hZ hE hw W N).hom ≫
        G[W].map (frobeniusColimitResChart p hX h c).hom ≫
        (frobeniusColimitLocalSolution p b z q e hX hX' hZ hE hw T n β h).inv :=
  CategoryTheory.resLam _ _ _ _ _ _ _ _ _ _
    (fun M => frobeniusColimitLocRestrictIso p b z q e hX hX' hZ hE hw V M)
    (fun M => frobeniusColimitLocRestrictIso p b z q e hX hX' hZ hE hw W M)
    (frobeniusColimitLocNestedNatIso p b z q e hX hX' hZ hE hw h) _
    (frobeniusColimitLocRestrictComp_locIso p b z q e hX hX' hZ hE hw h N) c _ β

/-- **Zariski glueing for the comparison functor of [Stacks, Tag 0EXD].** -/
theorem mem_essImage_frobeniusColimitVectorBundlesComparison_of_cover {J : Type u}
    (V : J → X.Opens) (hV : ⨆ j, V j = ⊤) (m : J → ℕ)
    (T : CategoricalPullback (frobeniusColimitVectorBundlesPullback p e hE hZ)
      (frobeniusColimitVectorBundlesPullback p q hE hX'))
    (β : ∀ j, G[V j].obj F[V j, m j] ≅ L[V j].obj T)
    (hfull : ∀ j k, G[V j ⊓ V k].Full) (hfaith : ∀ j k, G[V j ⊓ V k].Faithful)
    (hfaith₃ : ∀ j k l, G[V j ⊓ V k ⊓ V l].Faithful) :
    (frobeniusColimitVectorBundlesComparison p b z q e hX hX' hZ hE hw).essImage T := by
  classical
  let ρ : ∀ j {W : X.Opens} (_ : W ≤ V j), L[W].obj T ≅ G[W].obj F[W, m j] := fun j W h =>
    frobeniusColimitLocalSolution p b z q e hX hX' hZ hE hw T (m j) (β j) h
  let θ : ∀ j k, F[V j ⊓ V k, m j] ≅ F[V j ⊓ V k, m k] := fun j k =>
    G[V j ⊓ V k].preimageIso ((ρ j inf_le_left).symm ≪≫ ρ k inf_le_right)
  have hθ : ∀ j k, G[V j ⊓ V k].map (θ j k).hom =
      (ρ j inf_le_left).inv ≫ (ρ k inf_le_right).hom := fun j k =>
    G[V j ⊓ V k].map_preimage _
  have hid : ∀ j, (θ j j).hom = 𝟙 _ := fun j => by
    refine G[V j ⊓ V j].map_injective ?_
    rw [hθ, CategoryTheory.Functor.map_id]
    exact Iso.inv_hom_id _
  have hres : ∀ j k {W : X.Opens} (h : W ≤ V j ⊓ V k),
      G[W].map (frobeniusColimitFreeResIso p hX h (θ j k)).hom =
        (ρ j (h.trans inf_le_left)).inv ≫ (ρ k (h.trans inf_le_right)).hom := fun j k W h =>
    frobeniusColimitFreeRes_localSolution p b z q e hX hX' hZ hE hw T (β j) (β k)
      inf_le_left inf_le_right h (θ j k).hom (hθ j k)
  have hcocycle : ∀ j k l,
      (frobeniusColimitFreeResIso p hX (inf_le_left : V j ⊓ V k ⊓ V l ≤ V j ⊓ V k) (θ j k)).hom ≫
        (frobeniusColimitFreeResIso p hX
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
            V j ⊓ V k ⊓ V l ≤ V k ⊓ V l) (θ k l)).hom =
      (frobeniusColimitFreeResIso p hX
          (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            V j ⊓ V k ⊓ V l ≤ V j ⊓ V l) (θ j l)).hom := fun j k l => by
    refine G[V j ⊓ V k ⊓ V l].map_injective ?_
    rw [CategoryTheory.Functor.map_comp, hres, hres, hres, Category.assoc,
      Iso.hom_inv_id_assoc]
  obtain ⟨N, c, hc⟩ := exists_frobeniusColimitVectorBundle_glue p hX V hV m θ hid hcocycle
  let lam : ∀ j, L[V j].obj ((frobeniusColimitVectorBundlesComparison p b z q e hX hX' hZ hE
      hw).obj N) ≅ L[V j].obj T := fun j =>
    frobeniusColimitLocRestrictIso p b z q e hX hX' hZ hE hw (V j) N ≪≫ G[V j].mapIso (c j) ≪≫
      β j
  have hι : ∀ j k, frobeniusColimitLocResHom p b z q e hX' hZ hE hw
        (inf_le_left : V j ⊓ V k ≤ V j) (lam j).hom =
      frobeniusColimitLocResHom p b z q e hX' hZ hE hw
        (inf_le_right : V j ⊓ V k ≤ V k) (lam k).hom := fun j k => by
    have key : G[V j ⊓ V k].map (frobeniusColimitResChart p hX inf_le_left (c j)).hom ≫
          (ρ j inf_le_left).inv =
        G[V j ⊓ V k].map (frobeniusColimitResChart p hX inf_le_right (c k)).hom ≫
          (ρ k inf_le_right).inv := by
      rw [← hc j k, CategoryTheory.Functor.map_comp, hθ, Category.assoc, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    exact (frobeniusColimitLocResHom_chart p b z q e hX hX' hZ hE hw T N inf_le_left (c j)
      (β j)).trans ((whisker_eq _ key).trans
        (frobeniusColimitLocResHom_chart p b z q e hX hX' hZ hE hw T N inf_le_right (c k)
          (β k)).symm)
  exact ⟨N, nonempty_iso_of_frobeniusColimitLocRestrict p b z q e hX' hZ hE hw V hV _ T lam hι⟩

end AlgebraicGeometry
