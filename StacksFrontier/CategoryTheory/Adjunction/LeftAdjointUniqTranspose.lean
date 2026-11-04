module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksFrontier.CategoryTheory.Adjunction.Mates

/-!
# Transposing across either of two adjunctions with the same right adjoint

Two left adjoints of the same functor are isomorphic, by
`CategoryTheory.Adjunction.leftAdjointUniq`.  This file records what that isomorphism does to a
*transpose*: composing with it carries the transpose for one adjunction to the transpose for the
other.

## Main results

* `CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_inv_app_comp`: the transpose of a morphism
  out of one of two left adjoints of the same functor, precomposed with the comparison of the two
  left adjoints, is its transpose for the other adjunction.
-/

@[expose] public section

universe v₀ v₁ u₀ u₁

namespace CategoryTheory.Adjunction

open CategoryTheory

/-- The transpose of a morphism out of one of two left adjoints of the same functor, precomposed
with the comparison of the two left adjoints, is its transpose for the other adjunction.

This is `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` read through
`CategoryTheory.Adjunction.homEquiv_unit`. -/
public theorem homEquiv_leftAdjointUniq_inv_app_comp {C : Type u₀} {D : Type u₁} [Category.{v₀} C]
    [Category.{v₁} D] {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) (M : C) {N : D}
    (φ : F.obj M ⟶ N) :
    adj2.homEquiv M N ((leftAdjointUniq adj1 adj2).inv.app M ≫ φ) = adj1.homEquiv M N φ := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    ← Adjunction.unit_leftAdjointUniq_hom_app adj1 adj2, Category.assoc,
    ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app_assoc]

/-- **The `inv` transposition identity with the comparison of the two left adjoints left
opaque**, given instead as an isomorphism `e` together with the equation identifying it with
`CategoryTheory.Adjunction.leftAdjointUniq`.

This is to `CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_inv_app_comp` what
`CategoryTheory.Adjunction.homEquiv_eq_of_eq_leftAdjointUniq_ofNatIsoRight_symm` is to the `hom`
form, and it exists for the same reason: at concrete adjunctions, writing
`…leftAdjointUniq` under a hom-set bijection forces the elaborator to reduce the comparison to a
structure, which reaches the two adjunctions' data. On the two composite adjunctions of
`Stacks.SheafOfModules.sheafificationCompRestrictIso`, that is a deterministic `isDefEq` timeout.
With `e` a variable nothing reduces, and the consumer supplies the equation separately as a `rfl`
against its own definition. -/
public theorem homEquiv_eq_of_eq_leftAdjointUniq_inv_app_comp {C : Type u₀} {D : Type u₁}
    [Category.{v₀} C] [Category.{v₁} D] {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
    (e : F ≅ F') (he : e = leftAdjointUniq adj1 adj2) (M : C) {N : D} (φ : F.obj M ⟶ N) :
    adj2.homEquiv M N (e.inv.app M ≫ φ) = adj1.homEquiv M N φ := by
  subst he
  exact homEquiv_leftAdjointUniq_inv_app_comp adj1 adj2 M φ

/-- **The two inverse transposes of one morphism, along two adjunctions with the same right
adjoint, differ by the comparison of the left adjoints.**  The comparison followed by the
inverse transpose taken in the second adjunction is the inverse transpose taken in the first.

This is the `Equiv.symm` form of
`CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app_comp`. -/
public theorem leftAdjointUniq_hom_app_comp_homEquiv_symm'' {C : Type u₀} {D : Type u₁}
    [Category.{v₀} C] [Category.{v₁} D] {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
    {x : C} {y : D} (t : x ⟶ G.obj y) :
    (leftAdjointUniq adj1 adj2).hom.app x ≫ (adj2.homEquiv x y).symm t =
      (adj1.homEquiv x y).symm t :=
  (adj1.homEquiv x y).injective <| by
    rw [homEquiv_leftAdjointUniq_hom_app_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- **Whether an inverse transpose is an isomorphism does not depend on which of two adjunctions
with the same right adjoint it is taken in.**  The two inverse transposes differ by the
comparison of the left adjoints, which is an isomorphism.

The statement is symmetric in the two adjunctions, so this one biconditional supplies both
implications; `leftAdjointUniq` is available for either order of the pair. -/
public theorem isIso_homEquiv_symm_iff {C : Type u₀} {D : Type u₁} [Category.{v₀} C]
    [Category.{v₁} D] {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) {x : C} {y : D}
    (t : x ⟶ G.obj y) :
    IsIso ((adj1.homEquiv x y).symm t) ↔ IsIso ((adj2.homEquiv x y).symm t) := by
  rw [← leftAdjointUniq_hom_app_comp_homEquiv_symm'' adj1 adj2 t]
  exact CategoryTheory.isIso_comp_left_iff _ _

/-- **The transpose identity for two adjunctions whose right adjoints agree only up to a given
isomorphism.**  If `adj1 : F ⊣ G` and `adj2 : F' ⊣ G'` and `i : G ≅ G'`, the two left adjoints
are compared by `CategoryTheory.Adjunction.leftAdjointUniq` after turning `adj1` along `i`;
transposing the comparison followed by a morphism out of `F'` is then the transpose for `adj2`,
followed by the component of `i.inv`.

The transpose on the left is taken in `adj1` itself, not in `adj1.ofNatIsoRight i`, so that
`CategoryTheory.Adjunction.ofNatIsoRight` occurs in no type here or at a use site.

This is `CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app_comp` at
`adj1.ofNatIsoRight i`, read through
`CategoryTheory.Adjunction.homEquiv_ofNatIsoRight_apply`. -/
public theorem homEquiv_leftAdjointUniq_ofNatIsoRight_hom_app_comp {C : Type u₀} {D : Type u₁}
    [Category.{v₀} C] [Category.{v₁} D] {F F' : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G)
    (adj2 : F' ⊣ G') (i : G ≅ G') {x : C} {y : D} (k : F'.obj x ⟶ y) :
    adj1.homEquiv x y
          ((leftAdjointUniq (adj1.ofNatIsoRight i) adj2).hom.app x ≫ k) =
      adj2.homEquiv x y k ≫ i.inv.app y :=
  (Iso.eq_comp_inv (i.app y)).mpr
    ((Adjunction.homEquiv_ofNatIsoRight_apply adj1 i
          ((leftAdjointUniq (adj1.ofNatIsoRight i) adj2).hom.app x ≫ k)).symm.trans
      (homEquiv_leftAdjointUniq_hom_app_comp (adj1.ofNatIsoRight i) adj2 k))

/-- **The transpose identity with the comparison of the two left adjoints left opaque**, given
instead as an isomorphism `e` together with the equation identifying it with
`CategoryTheory.Adjunction.leftAdjointUniq` of the turned `adj1` against `adj2`.  The comparison
of the two right adjoints is taken in the direction `G' ≅ G`, pointing *onto* the right adjoint
of `adj1`, so that the factor left over is its `CategoryTheory.Iso.hom`.

This is the form a consumer can use.
`CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_ofNatIsoRight_hom_app_comp` cannot always be
used directly: its statement puts a `…leftAdjointUniq` under a hom-set bijection, and projecting
`CategoryTheory.Iso.hom` out of that against an expected type asks the elaborator to reduce the
comparison to a structure, which reaches the two adjunctions' data. Where those adjoints are
concrete that reduction is unbounded, and it is unbounded whether the comparison is named by a
definition to be unfolded or written out in full.

Here `e` is a variable, so nothing reduces: the identity is proved by `subst` and the consumer
supplies the equation separately, as a `rfl` against its own definition, where the one
definitional step it needs is affordable. -/
public theorem homEquiv_eq_of_eq_leftAdjointUniq_ofNatIsoRight_symm {C : Type u₀}
    {D : Type u₁} [Category.{v₀} C] [Category.{v₁} D] {F F' : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G)
    (adj2 : F' ⊣ G') (j : G' ≅ G) (e : F ≅ F')
    (he : e = leftAdjointUniq (adj1.ofNatIsoRight j.symm) adj2) {x : C} {y : D}
    (k : F'.obj x ⟶ y) :
    adj1.homEquiv x y (e.hom.app x ≫ k) = adj2.homEquiv x y k ≫ j.hom.app y := by
  subst he
  exact homEquiv_leftAdjointUniq_ofNatIsoRight_hom_app_comp adj1 adj2 j.symm k

end CategoryTheory.Adjunction

end
