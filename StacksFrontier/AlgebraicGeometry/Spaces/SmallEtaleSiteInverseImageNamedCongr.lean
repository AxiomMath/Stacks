module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSiteBaseChangeSquare

/-!
# The named-composite inverse-image comparison at a component

`AlgebraicGeometry.Space.siteInverseImageComp'` is the comparison `(f ≫ g)^* ≅ g^* ⋙ f^*` of
**Stacks 03LU** with the composite carried as a named morphism together with an equation naming
it.  This file supplies the componentwise identities the horizontal pasting law of
**Stacks 0E47** asks of it:  its compatibility with an equality of either of its two morphisms,
and its associativity pentagon read at an object — in the general form, and in the two forms
where only the threefold composite is named.

## Main results

* `Stacks.CategoryTheory.congr_inv_app_of_eqToIso_trans` and
  `Stacks.CategoryTheory.map_congr_inv_app_of_eqToIso_trans`: the transport bookkeeping the two
  compatibilities consist of, on variables.
* `AlgebraicGeometry.Space.siteInverseImageComp_assoc_named_app`,
  `AlgebraicGeometry.Space.siteInverseImageComp_assoc_right_app` and
  `AlgebraicGeometry.Space.siteInverseImageComp_assoc_left_app`: the pentagon at an object with
  only the threefold composite carried as a named morphism — the three shapes the pasting
  argument uses, according to which bracketings the rectangle hands it.
* `AlgebraicGeometry.Space.siteInverseImageComp'_congr_left` and
  `AlgebraicGeometry.Space.siteInverseImageComp'_congr_right`: compatibility with an equality of
  the inner respectively the outer morphism.  These are
  `AlgebraicGeometry.Space.siteInverseImageComp_congr_left` and `_congr_right` with each
  composite carried as a named morphism, which is what lets the two bracketings of a threefold
  composite meet in one equation.
* `AlgebraicGeometry.Space.siteInverseImageComp'_assoc_app`: the associativity pentagon at an
  object, in the orientation
  `Stacks.Cohomology.DerivedBaseChangePasting.squareComparison_horizontal` consumes.

## Implementation notes

The two bracketings of a threefold composite of morphisms of algebraic spaces are definitionally
equal, but deciding this between the objects `(siteInverseImage ((f'' ≫ h) ≫ g)).obj M` and
`(siteInverseImage (f'' ≫ h ≫ g)).obj M` times out; carrying each composite as a named morphism
keeps the check at the level of functors, where it is
`AlgebraicGeometry.Space.siteInverseImageComp'_rfl`. For the same reason each lemma here is a
single application of `Stacks.CategoryTheory.congr_inv_app_of_eqToIso_trans` or of
`CategoryTheory.Functor.pentagon_app_of_trans_assoc` rather than a tactic proof at a component.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor
open Stacks.Cohomology.DerivedBaseChangePasting (transportNatTrans transportNatTrans_app)

namespace Stacks.CategoryTheory

/-- The transport bookkeeping shared by the two congruence lemmas below, with the morphism `t`
between the two composites left abstract. -/
private theorem congr_inv_app_of_eqToIso_trans_aux {B C : Type*} [Category* B] [Category* C]
    {X₁ X₂ K₁ K₂ L₁ L₂ : C ⥤ B} {C₁ : K₁ ≅ X₁} {C₂ : K₂ ≅ X₂} {D₁ : L₁ ≅ X₁} {D₂ : L₂ ≅ X₂}
    {q : K₁ = K₂} {r₁ : L₁ = K₁} {r₂ : L₂ = K₂} {s : L₁ = L₂}
    (h₁ : D₁ = eqToIso r₁ ≪≫ C₁) (h₂ : D₂ = eqToIso r₂ ≪≫ C₂) {M : C} {t : X₁.obj M ⟶ X₂.obj M}
    (h : t ≫ C₂.inv.app M = C₁.inv.app M ≫ (transportNatTrans q).app M) :
    t ≫ D₂.inv.app M = D₁.inv.app M ≫ (transportNatTrans s).app M := by
  subst h₁
  subst h₂
  simp only [Iso.trans_inv, eqToIso.inv, NatTrans.comp_app, eqToHom_app,
    transportNatTrans_app, Category.assoc] at h ⊢
  rw [reassoc_of% h]
  simp only [eqToHom_trans]

/-- **Transporting a congruence identity across two comparisons presented as
`eqToIso _ ≪≫ _`.**  Given the identity for the two comparisons `C₁`, `C₂` — a morphism `u`
between the two composites, commuting with their inverses up to the transport along `q` — the
same identity holds for any two comparisons `D₁`, `D₂` that factor as a transport followed by
`C₁` respectively `C₂`, with the transport along the equality `s` of *their* sources.  No
compatibility between `q`, `r₁`, `r₂` and `s` has to be supplied:  the two composites of
transports are then transports along two proofs of one equality of objects. -/
theorem congr_inv_app_of_eqToIso_trans {A B C : Type*} [Category* A] [Category* B] [Category* C]
    {G : C ⥤ A} {F₁ F₂ : A ⥤ B} {K₁ K₂ L₁ L₂ : C ⥤ B}
    (C₁ : K₁ ≅ G ⋙ F₁) (C₂ : K₂ ≅ G ⋙ F₂) (D₁ : L₁ ≅ G ⋙ F₁) (D₂ : L₂ ≅ G ⋙ F₂)
    (p : F₁ = F₂) (q : K₁ = K₂) (r₁ : L₁ = K₁) (r₂ : L₂ = K₂) (s : L₁ = L₂)
    (h₁ : D₁ = eqToIso r₁ ≪≫ C₁) (h₂ : D₂ = eqToIso r₂ ≪≫ C₂) (M : C)
    (h : (transportNatTrans p).app (G.obj M) ≫ C₂.inv.app M =
      C₁.inv.app M ≫ (transportNatTrans q).app M) :
    (transportNatTrans p).app (G.obj M) ≫ D₂.inv.app M =
      D₁.inv.app M ≫ (transportNatTrans s).app M :=
  congr_inv_app_of_eqToIso_trans_aux h₁ h₂ h

/-- The companion of `Stacks.CategoryTheory.congr_inv_app_of_eqToIso_trans` for an equality of
the *inner* functor of the composite, where the transport is carried by the outer functor
instead of being read at a shifted object. -/
theorem map_congr_inv_app_of_eqToIso_trans {A B C : Type*}
    [Category* A] [Category* B] [Category* C]
    {G₁ G₂ : C ⥤ A} {F : A ⥤ B} {K₁ K₂ L₁ L₂ : C ⥤ B}
    (C₁ : K₁ ≅ G₁ ⋙ F) (C₂ : K₂ ≅ G₂ ⋙ F) (D₁ : L₁ ≅ G₁ ⋙ F) (D₂ : L₂ ≅ G₂ ⋙ F)
    (p : G₁ = G₂) (q : K₁ = K₂) (r₁ : L₁ = K₁) (r₂ : L₂ = K₂) (s : L₁ = L₂)
    (h₁ : D₁ = eqToIso r₁ ≪≫ C₁) (h₂ : D₂ = eqToIso r₂ ≪≫ C₂) (M : C)
    (h : F.map ((transportNatTrans p).app M) ≫ C₂.inv.app M =
      C₁.inv.app M ≫ (transportNatTrans q).app M) :
    F.map ((transportNatTrans p).app M) ≫ D₂.inv.app M =
      D₁.inv.app M ≫ (transportNatTrans s).app M :=
  congr_inv_app_of_eqToIso_trans_aux h₁ h₂ h

end Stacks.CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {T X Y Z : AlgebraicSpaces B S hS}

/-- **Compatibility of the named-composite inverse-image comparison with an equality of the
inner morphism.**  This is `AlgebraicGeometry.Space.siteInverseImageComp_congr_left` with both
composites carried as named morphisms. -/
theorem siteInverseImageComp'_congr_left {f f' : X ⟶ Y} (e : f = f') (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) (fg' : X ⟶ Z) (hfg' : fg' = f' ≫ g) (efg : fg = fg')
    (M : SiteModules B S hS Z) :
    (transportNatTrans (congrArg (fun k : X ⟶ Y => siteInverseImage k) e)).app
          ((siteInverseImage g).obj M) ≫ (siteInverseImageComp' f' g fg' hfg').inv.app M =
      (siteInverseImageComp' f g fg hfg).inv.app M ≫
        (transportNatTrans
          (congrArg (siteInverseImage (B := B) (S := S) (hS := hS)) efg)).app M :=
  Stacks.CategoryTheory.congr_inv_app_of_eqToIso_trans (siteInverseImageComp f g)
    (siteInverseImageComp f' g) (siteInverseImageComp' f g fg hfg)
    (siteInverseImageComp' f' g fg' hfg')
    (congrArg (fun k : X ⟶ Y => siteInverseImage k) e)
    (congrArg (fun k : X ⟶ Y => siteInverseImage (k ≫ g)) e)
    (congrArg (siteInverseImage (B := B) (S := S) (hS := hS)) hfg)
    (congrArg (siteInverseImage (B := B) (S := S) (hS := hS)) hfg')
    (congrArg (siteInverseImage (B := B) (S := S) (hS := hS)) efg)
    (siteInverseImageComp'_def f g fg hfg) (siteInverseImageComp'_def f' g fg' hfg') M
    (siteInverseImageComp_congr_left e g M)

/-- **Compatibility of the named-composite inverse-image comparison with an equality of the
outer morphism.**  This is `AlgebraicGeometry.Space.siteInverseImageComp_congr_right` with both
composites carried as named morphisms. -/
theorem siteInverseImageComp'_congr_right (f : X ⟶ Y) {g g' : Y ⟶ Z} (e : g = g')
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) (fg' : X ⟶ Z) (hfg' : fg' = f ≫ g') (efg : fg = fg')
    (M : SiteModules B S hS Z) :
    (siteInverseImage f).map
          ((transportNatTrans (congrArg (fun k : Y ⟶ Z => siteInverseImage k) e)).app M) ≫
        (siteInverseImageComp' f g' fg' hfg').inv.app M =
      (siteInverseImageComp' f g fg hfg).inv.app M ≫
        (transportNatTrans
          (congrArg (siteInverseImage (B := B) (S := S) (hS := hS)) efg)).app M :=
  Stacks.CategoryTheory.map_congr_inv_app_of_eqToIso_trans (siteInverseImageComp f g)
    (siteInverseImageComp f g') (siteInverseImageComp' f g fg hfg)
    (siteInverseImageComp' f g' fg' hfg')
    (congrArg (fun k : Y ⟶ Z => siteInverseImage k) e)
    (congrArg (fun k : Y ⟶ Z => siteInverseImage (f ≫ k)) e)
    (congrArg (siteInverseImage (B := B) (S := S) (hS := hS)) hfg)
    (congrArg (siteInverseImage (B := B) (S := S) (hS := hS)) hfg')
    (congrArg (siteInverseImage (B := B) (S := S) (hS := hS)) efg)
    (siteInverseImageComp'_def f g fg hfg) (siteInverseImageComp'_def f g' fg' hfg') M
    (siteInverseImageComp_congr_right f e M)

/-- **The associativity pentagon for the named-composite inverse-image comparison, at an
object.**  It is the isomorphism form `AlgebraicGeometry.Space.siteInverseImageComp'_assoc` read
at `M` through `CategoryTheory.Functor.pentagon_app_of_trans_assoc`, which is the orientation
the pasting argument
`Stacks.Cohomology.DerivedBaseChangePasting.squareComparison_horizontal` consumes. -/
theorem siteInverseImageComp'_assoc_app (f : T ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (gh : X ⟶ Z) (hgh : gh = g ≫ h) (fg : T ⟶ Y) (hfg : fg = f ≫ g)
    (fgh : T ⟶ Z) (e₁ : fgh = fg ≫ h) (e₂ : fgh = f ≫ gh) (M : SiteModules B S hS Z) :
    (siteInverseImageComp' f g fg hfg).inv.app ((siteInverseImage h).obj M) ≫
        (siteInverseImageComp' fg h fgh e₁).inv.app M =
      (siteInverseImage f).map ((siteInverseImageComp' g h gh hgh).inv.app M) ≫
        (siteInverseImageComp' f gh fgh e₂).inv.app M :=
  pentagon_app_of_trans_assoc (siteInverseImageComp' g h gh hgh).symm
    (siteInverseImageComp' f g fg hfg).symm (siteInverseImageComp' fg h fgh e₁).symm
    (siteInverseImageComp' f gh fgh e₂).symm
    (siteInverseImageComp'_assoc f g h gh hgh fg hfg fgh e₁ e₂) M

/-! ### The pentagon with only the threefold composite named -/

/-- **The pentagon of Stacks 03LU with only the threefold composite named.**  The two twofold
composites are written out, so the two comparisons `f^* ∘ g^*` and `g^* ∘ h^*` are the unprimed
ones;  the threefold composite is a named morphism `fgh` together with an equation naming it in
each of its two bracketings, which is what lets both appear in one equation.  This is
`AlgebraicGeometry.Space.siteInverseImageComp'_assoc` with the two naming equations that are
`rfl` discharged. -/
theorem siteInverseImageComp_assoc_named (f : T ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (fgh : T ⟶ Z)
    (e₁ : fgh = (f ≫ g) ≫ h) (e₂ : fgh = f ≫ g ≫ h) :
    (isoWhiskerRight (siteInverseImageComp g h).symm (siteInverseImage f)).symm ≪≫
        associator (siteInverseImage h) (siteInverseImage g) (siteInverseImage f) ≪≫
        isoWhiskerLeft (siteInverseImage h) (siteInverseImageComp f g).symm ≪≫
        (siteInverseImageComp' (f ≫ g) h fgh e₁).symm =
      (siteInverseImageComp' f (g ≫ h) fgh e₂).symm := by
  have H := siteInverseImageComp'_assoc f g h (g ≫ h) rfl (f ≫ g) rfl fgh e₁ e₂
  rw [siteInverseImageComp'_rfl, siteInverseImageComp'_rfl] at H
  exact H

/-- `AlgebraicGeometry.Space.siteInverseImageComp_assoc_named` with the threefold composite
taken to be `f ≫ g ≫ h`, so that the comparison on the right-hand side is the unprimed one. -/
theorem siteInverseImageComp_assoc_right (f : T ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (isoWhiskerRight (siteInverseImageComp g h).symm (siteInverseImage f)).symm ≪≫
        associator (siteInverseImage h) (siteInverseImage g) (siteInverseImage f) ≪≫
        isoWhiskerLeft (siteInverseImage h) (siteInverseImageComp f g).symm ≪≫
        (siteInverseImageComp' (f ≫ g) h (f ≫ g ≫ h) (Category.assoc f g h).symm).symm =
      (siteInverseImageComp f (g ≫ h)).symm := by
  have H := siteInverseImageComp_assoc_named f g h (f ≫ g ≫ h) (Category.assoc f g h).symm rfl
  rw [siteInverseImageComp'_rfl] at H
  exact H

/-- `AlgebraicGeometry.Space.siteInverseImageComp_assoc_named` with the threefold composite
taken to be `(f ≫ g) ≫ h`, so that the comparison on the left-hand side is the unprimed one. -/
theorem siteInverseImageComp_assoc_left (f : T ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (isoWhiskerRight (siteInverseImageComp g h).symm (siteInverseImage f)).symm ≪≫
        associator (siteInverseImage h) (siteInverseImage g) (siteInverseImage f) ≪≫
        isoWhiskerLeft (siteInverseImage h) (siteInverseImageComp f g).symm ≪≫
        (siteInverseImageComp (f ≫ g) h).symm =
      (siteInverseImageComp' f (g ≫ h) ((f ≫ g) ≫ h) (Category.assoc f g h)).symm := by
  have H := siteInverseImageComp_assoc_named f g h ((f ≫ g) ≫ h) rfl (Category.assoc f g h)
  rw [siteInverseImageComp'_rfl] at H
  exact H

/-- `AlgebraicGeometry.Space.siteInverseImageComp_assoc_named` at an object. -/
theorem siteInverseImageComp_assoc_named_app (f : T ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (fgh : T ⟶ Z)
    (e₁ : fgh = (f ≫ g) ≫ h) (e₂ : fgh = f ≫ g ≫ h) (M : SiteModules B S hS Z) :
    (siteInverseImageComp f g).inv.app ((siteInverseImage h).obj M) ≫
        (siteInverseImageComp' (f ≫ g) h fgh e₁).inv.app M =
      (siteInverseImage f).map ((siteInverseImageComp g h).inv.app M) ≫
        (siteInverseImageComp' f (g ≫ h) fgh e₂).inv.app M :=
  pentagon_app_of_trans_assoc (siteInverseImageComp g h).symm (siteInverseImageComp f g).symm
    (siteInverseImageComp' (f ≫ g) h fgh e₁).symm
    (siteInverseImageComp' f (g ≫ h) fgh e₂).symm
    (siteInverseImageComp_assoc_named f g h fgh e₁ e₂) M

/-- `AlgebraicGeometry.Space.siteInverseImageComp_assoc_right` at an object. -/
theorem siteInverseImageComp_assoc_right_app (f : T ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (M : SiteModules B S hS Z) :
    (siteInverseImageComp f g).inv.app ((siteInverseImage h).obj M) ≫
        (siteInverseImageComp' (f ≫ g) h (f ≫ g ≫ h)
          (Category.assoc f g h).symm).inv.app M =
      (siteInverseImage f).map ((siteInverseImageComp g h).inv.app M) ≫
        (siteInverseImageComp f (g ≫ h)).inv.app M :=
  pentagon_app_of_trans_assoc (siteInverseImageComp g h).symm (siteInverseImageComp f g).symm
    (siteInverseImageComp' (f ≫ g) h (f ≫ g ≫ h) (Category.assoc f g h).symm).symm
    (siteInverseImageComp f (g ≫ h)).symm (siteInverseImageComp_assoc_right f g h) M

/-- `AlgebraicGeometry.Space.siteInverseImageComp_assoc_left` at an object. -/
theorem siteInverseImageComp_assoc_left_app (f : T ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (M : SiteModules B S hS Z) :
    (siteInverseImageComp f g).inv.app ((siteInverseImage h).obj M) ≫
        (siteInverseImageComp (f ≫ g) h).inv.app M =
      (siteInverseImage f).map ((siteInverseImageComp g h).inv.app M) ≫
        (siteInverseImageComp' f (g ≫ h) ((f ≫ g) ≫ h)
          (Category.assoc f g h)).inv.app M :=
  pentagon_app_of_trans_assoc (siteInverseImageComp g h).symm (siteInverseImageComp f g).symm
    (siteInverseImageComp (f ≫ g) h).symm
    (siteInverseImageComp' f (g ≫ h) ((f ≫ g) ≫ h) (Category.assoc f g h)).symm
    (siteInverseImageComp_assoc_left f g h) M

end AlgebraicGeometry.Space

end
