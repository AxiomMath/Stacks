module

public import StacksFrontier.CategoryTheory.Sites.SliceTopos.SubterminalSlice

/-!
# Restricting the extension by the empty set

Let `F` be a presheaf of subsingletons on `C` whose support is the essential image of a fully
faithful functor `j : D ⥤ C`, and let `H` be a presheaf on `D`.  The extension by the empty set
`extend F j hsupp H` is a presheaf on `C` which vanishes off that support; over an object in the
image of `j` its sections are the sections of `H`, because the object of `D` chosen above
`j.obj B` is canonically isomorphic to `B`.  This file records that identification.

## Main results

* `CategoryTheory.Stacks.Topos.Subterminal.restrictExtendIso` — the restriction of the extension
  by the empty set along `j` is `H`.
-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Stacks.Topos.Subterminal

open Opposite

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : Cᵒᵖ ⥤ Type w} {j : D ⥤ C} [j.Full] [j.Faithful]
  [∀ X : Cᵒᵖ, Subsingleton (F.obj X)]
  (hsupp : ∀ U : C, Nonempty (F.obj (op U)) → j.essImage U)
  (hmem : ∀ B : D, Nonempty (F.obj (op (j.obj B))))

omit [∀ (X : Cᵒᵖ), Subsingleton (F.obj X)] in
/-- The image under `j` of the inverse of `srcIsoSelf` is the inverse of `srcIso`. -/
theorem map_srcIsoSelf_inv (B : D) (s : F.obj (op (j.obj B))) :
    j.map (srcIsoSelf hsupp B s).inv = (srcIso hsupp s).inv :=
  (Iso.inv_eq_inv (j.mapIso (srcIsoSelf hsupp B s)) (srcIso hsupp s)).2
    (map_srcIsoSelf_hom hsupp B s)

omit [∀ (X : Cᵒᵖ), Subsingleton (F.obj X)] in
/-- Transporting a section of `H` from the object chosen above `j.obj B` down to `B` and back
is the identity, whichever sections of `F` over `j.obj B` the two transports are taken along. -/
theorem map_srcIsoSelf_hom_inv (H : Dᵒᵖ ⥤ Type w) {B : D} (s s' : F.obj (op (j.obj B)))
    (x : H.obj (op (srcObj hsupp s))) :
    H.map (srcIsoSelf hsupp B s').hom.op (H.map (srcIsoSelf hsupp B s).inv.op x) = x := by
  show H.map (srcIsoSelf hsupp B s).hom.op (H.map (srcIsoSelf hsupp B s).inv.op x) = x
  simp [← Functor.map_comp_apply, ← op_comp]

omit [∀ (X : Cᵒᵖ), Subsingleton (F.obj X)] in
/-- Transporting a section of `H` from `B` up to the object chosen above `j.obj B` and back is
the identity. -/
theorem map_srcIsoSelf_inv_hom (H : Dᵒᵖ ⥤ Type w) {B : D} (s : F.obj (op (j.obj B)))
    (t : H.obj (op B)) :
    H.map (srcIsoSelf hsupp B s).inv.op (H.map (srcIsoSelf hsupp B s).hom.op t) = t := by
  simp [← Functor.map_comp_apply, ← op_comp]

omit [∀ (X : Cᵒᵖ), Subsingleton (F.obj X)] in
include hsupp in
/-- **The chosen objects transport the morphisms of `D`.**  For a morphism `k : B ⟶ B'` of
`Dᵒᵖ`, the morphism of `D` that full faithfulness extracts from `j.map k.unop` becomes `k.unop`
itself once the chosen objects over `j.obj B` and `j.obj B'` are identified with `B` and `B'`. -/
theorem srcIsoSelf_inv_comp_srcHom {B B' : Dᵒᵖ} (k : B ⟶ B') (s : F.obj (op (j.obj B.unop))) :
    (srcIsoSelf hsupp B'.unop (F.map (j.map k.unop).op s)).inv ≫
        srcHom hsupp (j.map k.unop).op s = k.unop ≫ (srcIsoSelf hsupp B.unop s).inv := by
  apply j.map_injective
  simp [map_srcHom, map_srcIsoSelf_inv]

/-- At each object of `D`, the restriction of the extension by the empty set is `H`: a section
is a section of `F`, of which there is exactly one, together with a section of `H` over the
chosen object, which is canonically `B`. -/
noncomputable def restrictExtendApp (H : Dᵒᵖ ⥤ Type w) (B : Dᵒᵖ) :
    (j.op ⋙ extend F j hsupp H).obj B ≅ H.obj B where
  hom := ↾fun p ↦ H.map (srcIsoSelf hsupp B.unop p.1).inv.op p.2
  inv := ↾fun t ↦ ⟨(hmem B.unop).some,
    H.map (srcIsoSelf hsupp B.unop (hmem B.unop).some).hom.op t⟩
  hom_inv_id := by
    ext ⟨s, x⟩
    exact extend_ext hsupp (map_srcIsoSelf_hom_inv hsupp H _ s x)
  inv_hom_id := by
    ext t
    exact map_srcIsoSelf_inv_hom hsupp H _ t

/-- Restricting the extension by the empty set along `j` gives back `H`. -/
noncomputable def restrictExtendIso (H : Dᵒᵖ ⥤ Type w) :
    j.op ⋙ extend F j hsupp H ≅ H :=
  NatIso.ofComponents (restrictExtendApp hsupp hmem H) fun {B B'} k ↦ by
    ext p
    change H.map (srcIsoSelf hsupp B'.unop (F.map (j.map k.unop).op p.1)).inv.op
        (H.map (srcHom hsupp (j.map k.unop).op p.1).op p.2) =
      H.map k.unop.op (H.map (srcIsoSelf hsupp B.unop p.1).inv.op p.2)
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
      srcIsoSelf_inv_comp_srcHom]

/-- The isomorphism carries a section of the extension over `j.obj B` to its component in `H`,
transported along the canonical identification of the chosen object with `B`. -/
theorem restrictExtendIso_hom_app_apply (H : Dᵒᵖ ⥤ Type w) (B : Dᵒᵖ)
    (p : (j.op ⋙ extend F j hsupp H).obj B) :
    (restrictExtendIso hsupp hmem H).hom.app B p =
      H.map (srcIsoSelf hsupp B.unop p.1).inv.op p.2 :=
  rfl

/-- The inverse isomorphism pairs a section of `H` over `B`, transported to the chosen object,
with the unique section of `F` over `j.obj B`. -/
theorem restrictExtendIso_inv_app_apply (H : Dᵒᵖ ⥤ Type w) (B : Dᵒᵖ) (t : H.obj B) :
    (restrictExtendIso hsupp hmem H).inv.app B t =
      ⟨(hmem B.unop).some,
        H.map (srcIsoSelf hsupp B.unop (hmem B.unop).some).hom.op t⟩ :=
  rfl

end Stacks.Topos.Subterminal

end CategoryTheory

end
