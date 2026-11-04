module

public import Mathlib.CategoryTheory.Triangulated.TStructure.Induced

/-!
# The inclusion of a subcategory commutes with the induced truncations

Let `t` be a t-structure on a pretriangulated category `C` and let `P` be a triangulated
subcategory on which `t` induces a t-structure, `CategoryTheory.ObjectProperty.tStructure`. The
truncation functors of the induced t-structure are *not* defined as the restrictions of those of
`t` — they are produced by `CategoryTheory.Triangulated.TStructure.truncLT` from the defining
triangles of the induced t-structure — so the commutation of the inclusion `P.ι` with the two
families of truncations is a statement, and it is what this file proves.

The proof is the uniqueness of a truncation triangle. The defining triangle of the induced
t-structure at `X` is sent by `P.ι` to a distinguished triangle of `C` whose first vertex is
`t`-truncated above at `n` and whose third vertex is `t`-truncated below at `n + 1`, because the
two truncation properties of the induced t-structure are the properties of `t` on the underlying
object (`CategoryTheory.ObjectProperty.tStructure_isLE_iff` and `..._isGE_iff`). Mathlib's
`CategoryTheory.Triangulated.TStructure.isIso₁_truncLE_map_of_isGE` and
`..._isIso₂_truncGE_map_of_isLE` then invert the comparison maps, and
`CategoryTheory.Triangulated.TStructure.to_truncLE_obj_ext` and `..._from_truncGE_obj_ext`
identify the canonical comparison with the resulting isomorphism, which also gives its
naturality.

## Main definitions

* `CategoryTheory.ObjectProperty.ιTruncLEIso`: `ι(τ^{≤n}X) ≅ τ^{≤n}(ι X)`, naturally in `X`.
* `CategoryTheory.ObjectProperty.ιTruncGEIso`: `ι(τ^{≥n}X) ≅ τ^{≥n}(ι X)`, naturally in `X`.
* `CategoryTheory.ObjectProperty.ιTruncGELEIso`: `ι(τ^{≥a}τ^{≤b}X) ≅ τ^{≥a}τ^{≤b}(ι X)`,
  naturally in `X`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  (P : ObjectProperty C) [P.IsTriangulated] (t : TStructure C) [P.HasInducedTStructure t]

omit [IsTriangulated C] in
/-- The underlying object of a `τ^{≤n}` of the induced t-structure is `t`-truncated above
at `n`. -/
public lemma isLE_ι_obj_truncLE (n : ℤ) (X : P.FullSubcategory) :
    t.IsLE (P.ι.obj (((P.tStructure t).truncLE n).obj X)) n :=
  (P.tStructure_isLE_iff t _ n).mp inferInstance

omit [IsTriangulated C] in
/-- The underlying object of a `τ^{≥n}` of the induced t-structure is `t`-truncated below
at `n`. -/
public lemma isGE_ι_obj_truncGE (n : ℤ) (X : P.FullSubcategory) :
    t.IsGE (P.ι.obj (((P.tStructure t).truncGE n).obj X)) n :=
  (P.tStructure_isGE_iff t _ n).mp inferInstance

/-! ### Truncation above -/

/-- The canonical comparison `ι(τ^{≤n}X) ⟶ τ^{≤n}(ι X)`: the map `ι(τ^{≤n}X) ⟶ ι X` has a
`t`-truncated above source, so it factors through `τ^{≤n}(ι X)`. -/
public def ιTruncLEHom (n : ℤ) (X : P.FullSubcategory) :
    P.ι.obj (((P.tStructure t).truncLE n).obj X) ⟶ (t.truncLE n).obj (P.ι.obj X) :=
  haveI := P.isLE_ι_obj_truncLE t n X
  t.liftTruncLE (P.ι.map (((P.tStructure t).truncLEι n).app X)) n

omit [IsTriangulated C] in
/-- The comparison `ι(τ^{≤n}X) ⟶ τ^{≤n}(ι X)` followed by `τ^{≤n}(ι X) ⟶ ι X` is the image
under `ι` of `τ^{≤n}X ⟶ X`. -/
@[reassoc (attr := simp)]
public lemma ιTruncLEHom_ι (n : ℤ) (X : P.FullSubcategory) :
    P.ιTruncLEHom t n X ≫ (t.truncLEι n).app (P.ι.obj X) =
      P.ι.map (((P.tStructure t).truncLEι n).app X) :=
  have := P.isLE_ι_obj_truncLE t n X
  t.liftTruncLE_ι _ _

/-- The comparison `ι(τ^{≤n}X) ⟶ τ^{≤n}(ι X)` is an isomorphism. -/
public instance isIso_ιTruncLEHom (n : ℤ) (X : P.FullSubcategory) :
    IsIso (P.ιTruncLEHom t n X) := by
  have hA := P.isLE_ι_obj_truncLE t n X
  have h₃ := P.isGE_ι_obj_truncGE t (n + 1) X
  have hv : IsIso ((t.truncLE n).map (P.ι.map (((P.tStructure t).truncLEι n).app X))) :=
    t.isIso₁_truncLE_map_of_isGE
      (P.ι.mapTriangle.obj (((P.tStructure t).triangleLEGE n (n + 1) rfl).obj X))
      (P.ι.map_distinguished _
        ((P.tStructure t).triangleLEGE_distinguished n (n + 1) rfl X)) n (n + 1) rfl h₃
  have key : P.ιTruncLEHom t n X =
      inv ((t.truncLEι n).app (P.ι.obj (((P.tStructure t).truncLE n).obj X))) ≫
        (t.truncLE n).map (P.ι.map (((P.tStructure t).truncLEι n).app X)) := by
    refine t.to_truncLE_obj_ext ?_
    rw [P.ιTruncLEHom_ι, Category.assoc]
    have hnat := (t.truncLEι n).naturality (P.ι.map (((P.tStructure t).truncLEι n).app X))
    simp only [Functor.id_obj, Functor.id_map] at hnat
    rw [hnat, IsIso.inv_hom_id_assoc]
  rw [key]
  infer_instance

/-- **The inclusion commutes with truncation above.** `ι(τ^{≤n}X) ≅ τ^{≤n}(ι X)`, naturally
in `X`. -/
public def ιTruncLEIso (n : ℤ) :
    (P.tStructure t).truncLE n ⋙ P.ι ≅ P.ι ⋙ t.truncLE n :=
  NatIso.ofComponents (fun X => asIso (P.ιTruncLEHom t n X)) (by
    intro X Y f
    have : t.IsLE (((P.tStructure t).truncLE n ⋙ P.ι).obj X) n := P.isLE_ι_obj_truncLE t n X
    refine t.to_truncLE_obj_ext ?_
    dsimp only [Functor.comp_map, asIso_hom]
    rw [Category.assoc, Category.assoc, P.ιTruncLEHom_ι]
    have hnat := (t.truncLEι n).naturality (P.ι.map f)
    simp only [Functor.id_obj, Functor.id_map] at hnat
    rw [hnat, ← Functor.map_comp, P.ιTruncLEHom_ι_assoc, ← Functor.map_comp]
    exact congrArg P.ι.map (((P.tStructure t).truncLEι n).naturality f))

/-! ### Truncation below -/

/-- The canonical comparison `τ^{≥n}(ι X) ⟶ ι(τ^{≥n}X)`: the map `ι X ⟶ ι(τ^{≥n}X)` has a
`t`-truncated below target, so it factors through `τ^{≥n}(ι X)`. -/
public def ιTruncGEHom (n : ℤ) (X : P.FullSubcategory) :
    (t.truncGE n).obj (P.ι.obj X) ⟶ P.ι.obj (((P.tStructure t).truncGE n).obj X) :=
  haveI := P.isGE_ι_obj_truncGE t n X
  t.descTruncGE (P.ι.map (((P.tStructure t).truncGEπ n).app X)) n

omit [IsTriangulated C] in
/-- `ι X ⟶ τ^{≥n}(ι X)` followed by the comparison `τ^{≥n}(ι X) ⟶ ι(τ^{≥n}X)` is the image
under `ι` of `X ⟶ τ^{≥n}X`. -/
@[reassoc (attr := simp)]
public lemma π_ιTruncGEHom (n : ℤ) (X : P.FullSubcategory) :
    (t.truncGEπ n).app (P.ι.obj X) ≫ P.ιTruncGEHom t n X =
      P.ι.map (((P.tStructure t).truncGEπ n).app X) :=
  have := P.isGE_ι_obj_truncGE t n X
  t.π_descTruncGE _ _

/-- The comparison `τ^{≥n}(ι X) ⟶ ι(τ^{≥n}X)` is an isomorphism. -/
public instance isIso_ιTruncGEHom (n : ℤ) (X : P.FullSubcategory) :
    IsIso (P.ιTruncGEHom t n X) := by
  have hA := P.isGE_ι_obj_truncGE t n X
  have h₁ := P.isLE_ι_obj_truncLE t (n - 1) X
  have hv : IsIso ((t.truncGE n).map (P.ι.map (((P.tStructure t).truncGEπ n).app X))) :=
    t.isIso₂_truncGE_map_of_isLE
      (P.ι.mapTriangle.obj (((P.tStructure t).triangleLEGE (n - 1) n (by lia)).obj X))
      (P.ι.map_distinguished _
        ((P.tStructure t).triangleLEGE_distinguished (n - 1) n (by lia) X)) (n - 1) n (by lia) h₁
  have key : P.ιTruncGEHom t n X =
      (t.truncGE n).map (P.ι.map (((P.tStructure t).truncGEπ n).app X)) ≫
        inv ((t.truncGEπ n).app (P.ι.obj (((P.tStructure t).truncGE n).obj X))) := by
    refine t.from_truncGE_obj_ext ?_
    rw [P.π_ιTruncGEHom, ← Category.assoc]
    have hnat := (t.truncGEπ n).naturality (P.ι.map (((P.tStructure t).truncGEπ n).app X))
    simp only [Functor.id_obj, Functor.id_map] at hnat
    rw [← hnat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [key]
  infer_instance

/-- **The inclusion commutes with truncation below.** `ι(τ^{≥n}X) ≅ τ^{≥n}(ι X)`, naturally
in `X`. -/
public def ιTruncGEIso (n : ℤ) :
    (P.tStructure t).truncGE n ⋙ P.ι ≅ P.ι ⋙ t.truncGE n :=
  (NatIso.ofComponents (fun X => asIso (P.ιTruncGEHom t n X)) (by
    intro X Y f
    have : t.IsGE (((P.tStructure t).truncGE n ⋙ P.ι).obj Y) n := P.isGE_ι_obj_truncGE t n Y
    refine t.from_truncGE_obj_ext ?_
    dsimp only [Functor.comp_map, asIso_hom]
    rw [← Category.assoc, ← Category.assoc, P.π_ιTruncGEHom]
    have hnat := (t.truncGEπ n).naturality (P.ι.map f)
    simp only [Functor.id_obj, Functor.id_map] at hnat
    rw [← hnat, Category.assoc, P.π_ιTruncGEHom, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg P.ι.map (((P.tStructure t).truncGEπ n).naturality f))).symm

/-! ### The interval truncation -/

/-- **The inclusion commutes with the interval truncation.**
`ι(τ^{≥a}τ^{≤b}X) ≅ τ^{≥a}τ^{≤b}(ι X)`, naturally in `X`. This is the form the dévissage of
[Stacks, Tag 0G2H] uses, with `a = b = p`. -/
public def ιTruncGELEIso (a b : ℤ) :
    (P.tStructure t).truncGELE a b ⋙ P.ι ≅ P.ι ⋙ t.truncGELE a b :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((P.tStructure t).truncLE b) (P.ιTruncGEIso t a) ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (P.ιTruncLEIso t b) (t.truncGE a) ≪≫
          Functor.associator _ _ _

end CategoryTheory.ObjectProperty

end
