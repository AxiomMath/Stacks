module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Functor.Category

/-!
# Carrying a comparison across a change of ambient, generically

Let `F` be an endofunctor of a category which comes with a natural isomorphism to the identity —
the inverse image of modules along an identity morphism, in the application below.  A *comparison
assembled over an ambient* is a composite

```
A --s--→ Dcs ←-Pi-- Ci ←-uCi-- F.obj Ci --e--→ Cl
```

in which `Pi` is the inverse of a five-link chain whose first link is `uCi` and whose second is a
change-of-ambient isomorphism `e`.  Two such chains, one at an object and one at the ambient it is
read over, are carried to one another by the canonical map `k` of the change-of-ambient square,
and that is what `Stacks.CategoryTheory.change_of_ambient_of` says: with each link's
identification supplied as its own hypothesis, `F.map q ≫ k` is the natural isomorphism to the
identity followed by the two outer links.

Every morphism is a plain variable and every identification is a separate hypothesis: no
isomorphism is passed as a single term with both of its projections taken, and no composite is
written out at the point of use.  Both are deliberate — the geometric instance below
`AlgebraicGeometry.Space.conormalModuleOfImmersionRepresentedIso` hits a kernel
deterministic timeout when either is done otherwise.

## Main results

* `Stacks.CategoryTheory.eq_map_comp_of_conjugate`: a morphism conjugated by two inverse pairs,
  solved for itself.  This is what turns the identification of a change-of-ambient isomorphism
  with the canonical map of its square into a formula for that canonical map.
* `Stacks.CategoryTheory.change_of_ambient_of`: the change of ambient of a five-link comparison.
* `Stacks.CategoryTheory.trans4_hom`, `Stacks.CategoryTheory.symm_trans3_inv` and
  `Stacks.CategoryTheory.symm_trans_hom`: the forward and inverse maps of a composite of
  isomorphisms, written out.  These are the forms in which a chain of comparisons is handed to the
  lemmas above: the same equations proved by `rfl` at the geometric instance are kernel
  deterministic timeouts, and a term application of these is free.
* `Stacks.CategoryTheory.comp3_eq_of_transport` and `Stacks.CategoryTheory.comp4_comp_cancel`: a
  composite of transports collapses to its first factor, and a four-fold chain followed by a
  two-fold one cancels in the middle.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory

universe v₁ u₁

variable {D : Type u₁} [Category.{v₁} D]

/-- **A morphism conjugated by two inverse pairs, solved for itself.**  If `e` is `k` conjugated by
`F.map zi` in front and `zl` behind, then `k` is `e` conjugated the other way.

Read against the application: `e` is the change-of-ambient isomorphism of
[Stacks Project, Tag 04CO], `k` the canonical map of [Stacks Project, Tag 04CP] of the same square
at the kernel-ideal-power spelling, and `z`, `zl` the bridges of [Stacks Project, Tag 09RR] at the
two immersions. -/
theorem eq_map_comp_of_conjugate (F : D ⥤ D) {X Y X' Y' : D}
    (z : X ⟶ Y) (zi : Y ⟶ X) (k : F.obj X ⟶ X') (e : F.obj Y ⟶ Y')
    (zl : X' ⟶ Y') (zli : Y' ⟶ X')
    (h : e = F.map zi ≫ k ≫ zl) (hz : z ≫ zi = 𝟙 X) (hl : zl ≫ zli = 𝟙 X') :
    k = F.map z ≫ e ≫ zli := by
  rw [h]
  simp only [Category.assoc]
  rw [hl, Category.comp_id, ← Category.assoc (F.map z) (F.map zi) k, ← F.map_comp, hz,
    F.map_id, Category.id_comp]

/-- **The change of ambient of a five-link comparison, at variables.**

`Pi` is the inverse of a comparison whose chain begins with the natural isomorphism `uCi` to the
identity and continues with the change-of-ambient isomorphism `e` and a tail `r`; `q` is `Pi`
conjugated into the kernel-ideal-power spelling by `s` and `zi`; `k` is the canonical map of the
change-of-ambient square, written through `e` by
`Stacks.CategoryTheory.eq_map_comp_of_conjugate`; and `zL` is the comparison at the ambient,
related to the tail by `hzL`.

The conclusion is the naturality square of the two comparisons across `k`, which is the shape a
composition law for `k` consumes. -/
theorem change_of_ambient_of (F : D ⥤ D) {A Ci Cl Dcs KZi KZl : D}
    (uA : F.obj A ⟶ A) (uCi : F.obj Ci ⟶ Ci) (uiCi : Ci ⟶ F.obj Ci)
    (s : A ⟶ Dcs) (Pi : Dcs ⟶ Ci) (e : F.obj Ci ⟶ Cl) (ei : Cl ⟶ F.obj Ci)
    (r : Cl ⟶ Dcs) (ri : Dcs ⟶ Cl) (z : KZi ⟶ Ci) (zi : Ci ⟶ KZi)
    (zli : Cl ⟶ KZl) (q : A ⟶ KZi) (k : F.obj KZi ⟶ KZl) (zL : Dcs ⟶ KZl)
    (hq : q = s ≫ Pi ≫ zi) (hzz : zi ≫ z = 𝟙 Ci)
    (hk : k = F.map z ≫ e ≫ zli)
    (hPi : Pi = ri ≫ ei ≫ uCi)
    (hu : uCi ≫ uiCi = 𝟙 (F.obj Ci)) (hee : ei ≫ e = 𝟙 Cl) (hrr : ri ≫ r = 𝟙 Dcs)
    (hzL : r ≫ zL = zli)
    (hNat : F.map (s ≫ Pi) ≫ uCi = uA ≫ s ≫ Pi) :
    F.map q ≫ k = uA ≫ s ≫ zL := by
  have hzL' : ri ≫ zli = zL := by
    rw [← hzL, ← Category.assoc, hrr, Category.id_comp]
  have hu' : ∀ {W : D} (g : F.obj Ci ⟶ W), uCi ≫ uiCi ≫ g = g := fun g => by
    rw [← Category.assoc, hu, Category.id_comp]
  have hP : Pi ≫ uiCi ≫ e ≫ zli = zL := by
    rw [hPi]
    simp only [Category.assoc, hu']
    rw [← Category.assoc ei, hee, Category.id_comp, hzL']
  have key : F.map (s ≫ Pi) ≫ e ≫ zli = uA ≫ s ≫ zL :=
    calc F.map (s ≫ Pi) ≫ e ≫ zli
        = (F.map (s ≫ Pi) ≫ uCi) ≫ uiCi ≫ e ≫ zli := by rw [Category.assoc, hu']
      _ = uA ≫ s ≫ zL := by rw [hNat, ← hP]; simp only [Category.assoc]
  have h2 : (s ≫ Pi ≫ zi) ≫ z = s ≫ Pi := by
    simp only [Category.assoc, hzz, Category.comp_id]
  rw [hq, hk, ← Category.assoc (F.map (s ≫ Pi ≫ zi)) (F.map z) (e ≫ zli), ← F.map_comp, h2,
    key]

/-- **The forward map of a four-fold composite of isomorphisms.**  Proved by `rfl` at the
geometric instance of `AlgebraicGeometry.Space.conormalModuleOfImmersionRepresentedIso`'s tail it
is a kernel deterministic timeout; applied as a term it is free. -/
theorem trans4_hom {X₀ X₁ X₂ X₃ X₄ : D} (a : X₀ ≅ X₁) (b : X₁ ≅ X₂) (c : X₂ ≅ X₃)
    (d : X₃ ≅ X₄) : (a ≪≫ b ≪≫ c ≪≫ d).hom = a.hom ≫ b.hom ≫ c.hom ≫ d.hom :=
  rfl

/-- **The inverse of a three-fold composite whose first factor is given as an inverse.** -/
theorem symm_trans3_inv {X₀ X₁ X₂ X₃ : D} (a : X₁ ≅ X₀) (b : X₁ ≅ X₂) (c : X₂ ≅ X₃) :
    (a.symm ≪≫ b ≪≫ c).inv = c.inv ≫ b.inv ≫ a.hom :=
  Category.assoc _ _ _

/-- **The forward map of a composite whose first factor is given as an inverse.** -/
theorem symm_trans_hom {X₀ X₁ X₂ : D} (a : X₁ ≅ X₀) (b : X₁ ≅ X₂) :
    (a.symm ≪≫ b).hom = a.inv ≫ b.hom :=
  rfl

/-- **A composite of three transports collapses to its first factor.**  Each factor is a plain
morphism variable identified with its transport by its own hypothesis, so that no transport is
ever shared inside a composite. -/
theorem comp3_eq_of_transport {A X Y Z : D} (f : A ⟶ X) (p : X = Y) (q : Y = Z) (h : Z = X)
    (a : A ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ X)
    (ha : a = f ≫ (eqToIso p).hom) (hb : b = (eqToIso q).hom) (hc : c = eqToHom h) :
    a ≫ b ≫ c = f := by
  subst ha hb hc
  simp

/-- **A four-fold chain followed by a two-fold one, cancelling in the middle.**  The last two
factors of the chain are the inverse of the first factor of the tail, so that what is left is the
first two factors of the chain followed by the last factor of the tail. -/
theorem comp4_comp_cancel {A X Y Z W P : D} (a : A ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (d : Z ⟶ W)
    (g : W ⟶ Y) (gi : Y ⟶ W) (m : Y ⟶ P) (f : A ⟶ P) (t : A ⟶ W) (zl : W ⟶ P)
    (ht : t = a ≫ b ≫ c ≫ d) (hzl : zl = g ≫ m) (hcd : c ≫ d = gi)
    (hgg : gi ≫ g = 𝟙 Y) (hf : a ≫ b ≫ m = f) :
    t ≫ zl = f := by
  subst ht hzl
  simp only [Category.assoc]
  rw [← Category.assoc c d (g ≫ m), hcd, ← Category.assoc gi g m, hgg, Category.id_comp, hf]

end Stacks.CategoryTheory

end
