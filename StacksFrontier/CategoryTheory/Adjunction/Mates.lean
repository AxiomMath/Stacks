module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Changing the adjunction in a mate, and mates under the hom-set bijection

Let `L₁ ⊣ R` and `L₂ ⊣ R` be two adjunctions with the same right adjoint.  The two left
adjoints are canonically isomorphic, by `CategoryTheory.Adjunction.leftAdjointUniq`, and this
file records what that does to the mates correspondence: a 2-cell between right adjoints has
mates with respect to either adjunction, and the two mates differ by whiskering with the
canonical isomorphism.

The file also records how conjugates and mates act on individual morphisms through the
hom-set bijections of the adjunctions involved.  For a square of adjunctions, transposing a
morphism `L_a X ⟶ Y` along the bottom-right route and transposing it along the top-left route
differ exactly by the mate of the given 2-cell; this is the element-level form of the mates
correspondence, and it is what identifies a base-change comparison map on a square with the
transpose of a morphism.

## Main results

* `Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_hom`: the conjugate of the canonical
  comparison of two left adjoints of the same functor is the identity.
* `Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom`: for two adjunctions
  whose right adjoints are merely isomorphic, the conjugate of the canonical comparison of the
  left adjoints is the inverse of the given isomorphism of the right adjoints.
* `Stacks.CategoryTheory.mateEquiv_symm_eqToHom_comp_counit`: when the square of right adjoints
  commutes on the nose and the two further functors of the square themselves have left adjoints,
  the mate of that identity is pinned by one equation: its adjunct is the canonical comparison of
  the two left adjoints of the common right-adjoint composite, followed by the counit.
* `CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app_comp`: precomposition with the
  canonical comparison of two left adjoints of the same functor identifies the two hom-set
  bijections.
* `CategoryTheory.Adjunction.homEquiv_symm_comp_rightAdjointUniq_hom_app`: appending the canonical
  comparison of two right adjoints of isomorphic left adjoints changes an adjunct only by that
  isomorphism of left adjoints.
* `Stacks.CategoryTheory.mateEquiv_symm_congr_left` and
  `Stacks.CategoryTheory.mateEquiv_symm_congr_right`: replacing the left-hand (respectively
  right-hand) adjunction of a mate by another adjunction with the same right adjoint whiskers
  the mate by the canonical comparison of the two left adjoints.
* `Stacks.CategoryTheory.homEquiv_conjugate`: precomposing with the conjugate of a 2-cell
  between right adjoints transposes to postcomposing with that 2-cell.
* `Stacks.CategoryTheory.homEquiv_conjugate'`: the same identity with the 2-cell given on the
  left adjoints instead, which is the form in which a comparison of two left adjoints arrives.
* `Stacks.CategoryTheory.homEquiv_mate`: the same statement for a square of adjunctions, with
  the mate of the 2-cell in place of the 2-cell.
* `Stacks.CategoryTheory.mateEquiv_eq_of_counit`: the converse of
  `CategoryTheory.mateEquiv_counit` — a 2-cell between the right adjoints whose counit square
  commutes *is* the mate. Together the two make the counit square a characterization of the
  mate, which is what lets a comparison morphism built by other means be recognized as one.
* `Stacks.CategoryTheory.isIso_map_counit_of_isIso_mateEquiv_app` and
  `Stacks.CategoryTheory.isIso_map_mateEquiv_app_of_isIso_map_counit`: the counit square read
  as a factorization through three morphisms, so that invertibility transfers along it in
  either direction.

## Implementation notes

The first two statements are immediate from Mathlib's
`CategoryTheory.conjugateEquiv_mateEquiv_vcomp` and
`CategoryTheory.mateEquiv_conjugateEquiv_vcomp`, which compute the mate of a 2-cell
whiskered by a natural transformation on one side in terms of the conjugate of that
transformation.  The content is therefore entirely in
`conjugateEquiv_leftAdjointUniq_hom`, which says that the relevant conjugate is the identity;
that in turn is the triangle identity, via
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`.

`homEquiv_mate` is deduced from `homEquiv_conjugate` applied to the composite adjunctions
`a.comp b` and `c.comp d`, after which `CategoryTheory.Adjunction.comp_homEquiv` splits both
sides into the two one-step transposes and `CategoryTheory.unit_mateEquiv_symm` identifies the
remaining comparison.
-/

@[expose] public section

open CategoryTheory TwoSquare

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.Adjunction

/-- Transporting a morphism along the canonical isomorphism of two left adjoints of the same
functor and then taking its adjunct gives the adjunct for the second adjunction.

This is `CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app` with a morphism out of the
comparison's target appended. -/
theorem homEquiv_leftAdjointUniq_hom_app_comp {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {L L' : C ⥤ D} {R : D ⥤ C} (adj1 : L ⊣ R) (adj2 : L' ⊣ R) {x : C}
    {y : D} (h : L'.obj x ⟶ y) :
    adj1.homEquiv x y ((adj1.leftAdjointUniq adj2).hom.app x ≫ h) = adj2.homEquiv x y h := by
  rw [homEquiv_unit, homEquiv_unit, R.map_comp, ← Category.assoc,
    unit_leftAdjointUniq_hom_app]

/-- **The adjunct of a morphism composed with the canonical comparison of two right adjoints.**

Let `adj₁ : L₁ ⊣ P₁` and `adj₂ : L₂ ⊣ P₂` be adjunctions and `cmp : L₁ ≅ L₂` an isomorphism of
their left adjoints.  Transporting `adj₁` along `cmp` makes `P₁` and `P₂` two right adjoints of
`L₂`, hence compared by `CategoryTheory.Adjunction.rightAdjointUniq`; appending that comparison to
a morphism `h : W ⟶ P₁Z` changes its adjunct only by `cmp`.

This is what reduces an equation between two structure maps, one of them composed with the
comparison of the two direct images, to an equation between their inverse-image forms. -/
theorem homEquiv_symm_comp_rightAdjointUniq_hom_app {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {L₁ L₂ : C ⥤ D} {P₁ P₂ : D ⥤ C} (adj₁ : L₁ ⊣ P₁) (adj₂ : L₂ ⊣ P₂)
    (cmp : L₁ ≅ L₂) {W : C} {Z : D} (h : W ⟶ P₁.obj Z) :
    (adj₂.homEquiv W Z).symm
        (h ≫ (rightAdjointUniq (adj₁.ofNatIsoLeft cmp) adj₂).hom.app Z) =
      cmp.inv.app W ≫ (adj₁.homEquiv W Z).symm h := by
  rw [homEquiv_counit, Functor.map_comp, Category.assoc, rightAdjointUniq_hom_app_counit,
    ← homEquiv_counit, homEquiv_ofNatIsoLeft_symm_apply]

end CategoryTheory.Adjunction

namespace Stacks.CategoryTheory

variable {A : Type u₁} {B : Type u₂} {E : Type u₃} {F : Type u₄}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} E] [Category.{v₄} F]

/-- The conjugate, with respect to two adjunctions with the same right adjoint `R`, of the
canonical comparison of their left adjoints is the identity of `R`. -/
theorem conjugateEquiv_leftAdjointUniq_hom {L₁ L₂ : A ⥤ B} {R : B ⥤ A}
    (adj₁ : L₁ ⊣ R) (adj₂ : L₂ ⊣ R) :
    conjugateEquiv adj₂ adj₁ (Adjunction.leftAdjointUniq adj₁ adj₂).hom = 𝟙 R := by
  ext d
  simp only [conjugateEquiv_apply_app, NatTrans.id_app]
  rw [← Category.assoc, Adjunction.unit_leftAdjointUniq_hom_app,
    adj₂.right_triangle_components]

/-- Changing the right adjoint of an adjunction along an isomorphism `e : R ≅ R'` has `e.inv`
as the conjugate of the identity of the left adjoint. -/
theorem conjugateEquiv_ofNatIsoRight_id {L : A ⥤ B} {R R' : B ⥤ A} (adj : L ⊣ R) (e : R ≅ R') :
    conjugateEquiv (adj.ofNatIsoRight e) adj (𝟙 L) = e.inv := by
  ext d
  refine (adj.homEquiv (R'.obj d) d).symm.injective ?_
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, conjugateEquiv_counit]
  simp

/-- Let `adj : L ⊣ R` and `adj' : L' ⊣ R'` be adjunctions and `e : R ≅ R'` an isomorphism of
their right adjoints. Then `L` and `L'` are two left adjoints of `R'`, hence compared by
`CategoryTheory.Adjunction.leftAdjointUniq`, and the conjugate of that comparison is `e.inv`.

This is what fixes the normalization of the comparison of left adjoints induced by a comparison
of right adjoints: the comparison is the one whose mate is the given one. -/
theorem conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom
    {L L' : A ⥤ B} {R R' : B ⥤ A} (adj : L ⊣ R) (e : R ≅ R') (adj' : L' ⊣ R') :
    conjugateEquiv adj' adj
        (Adjunction.leftAdjointUniq (adj.ofNatIsoRight e) adj').hom = e.inv := by
  have h := conjugateEquiv_comp (adj₁ := adj') (adj₂ := adj.ofNatIsoRight e) (adj₃ := adj)
    (α := (Adjunction.leftAdjointUniq (adj.ofNatIsoRight e) adj').hom) (β := 𝟙 L)
  rw [conjugateEquiv_leftAdjointUniq_hom, conjugateEquiv_ofNatIsoRight_id] at h
  simp only [Category.id_comp] at h
  exact h.symm

/-- Transporting an adjunction along an *equality* of right adjoints transports its hom-set
bijection by the corresponding `eqToHom`. -/
theorem homEquiv_eq_rec {L : A ⥤ B} {R R' : B ⥤ A} (adj : L ⊣ R) (h : R = R') (X : A) (Y : B)
    (g : L.obj X ⟶ Y) :
    (h ▸ adj : L ⊣ R').homEquiv X Y g = adj.homEquiv X Y g ≫ (eqToHom h).app Y := by
  subst h
  simp

variable {G : A ⥤ E} {H : B ⥤ F}

/-- **The mate of a strict Beck–Chevalley identity, read through the lower shrieks.**

Let `L₁ ⊣ R₁`, `L₂ ⊣ R₂` be adjunctions and let `G`, `H` be the two further functors of a square
```
      A ⥤ B
    G ↓   ↓ H
      E ⥤ F
```
which themselves have left adjoints `G' ⊣ G` and `H' ⊣ H`.  Suppose the square of right adjoints
commutes on the nose, `R₁ ⋙ G = H ⋙ R₂`, and let `α` be the mate of that identity, a 2-cell
`G ⋙ L₂ ⟶ L₁ ⋙ H`.

Then the adjunct of `α` under `L₂ ⋙ H' ⊣ H ⋙ R₂` is the canonical comparison of the two left
adjoints of `H ⋙ R₂` — the other 2-cell the identity produces — followed by `L₁` of the counit of
`G' ⊣ G`.  Both sides are maps `H'(L₂(G X)) ⟶ L₁ X`, and the proof is the two triangle
identities: under the hom-set bijection both become `G(η₁)`.

This is the equation that pins the mate down: it determines `α` completely, since the adjunct is a
bijection. -/
theorem mateEquiv_symm_eqToHom_comp_counit {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    {G' : E ⥤ A} {H' : F ⥤ B} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adjG : G' ⊣ G) (adjH : H' ⊣ H)
    (h : R₁ ⋙ G = H ⋙ R₂) (X : A) :
    H'.map (((mateEquiv adj₁ adj₂).symm (eqToHom h)).app X) ≫ adjH.counit.app (L₁.obj X) =
      (Adjunction.leftAdjointUniq (adj₂.comp adjH)
          (h ▸ adjG.comp adj₁ : G' ⋙ L₁ ⊣ H ⋙ R₂)).hom.app (G.obj X) ≫
        L₁.map (adjG.counit.app X) := by
  apply ((adj₂.comp adjH).homEquiv (G.obj X) (L₁.obj X)).injective
  have hl : (adj₂.comp adjH).homEquiv (G.obj X) (L₁.obj X)
        (H'.map (((mateEquiv adj₁ adj₂).symm (eqToHom h)).app X) ≫
          adjH.counit.app (L₁.obj X)) =
      G.map (adj₁.unit.app X) ≫ (eqToHom h).app (L₁.obj X) := by
    rw [Adjunction.comp_homEquiv]
    simp only [Equiv.trans_apply]
    rw [← Adjunction.homEquiv_counit, Equiv.apply_symm_apply]
    exact (unit_mateEquiv_symm adj₁ adj₂ (eqToHom h) X).symm
  have hr : (adj₂.comp adjH).homEquiv (G.obj X) (L₁.obj X)
        ((Adjunction.leftAdjointUniq (adj₂.comp adjH)
            (h ▸ adjG.comp adj₁ : G' ⋙ L₁ ⊣ H ⋙ R₂)).hom.app (G.obj X) ≫
          L₁.map (adjG.counit.app X)) =
      G.map (adj₁.unit.app X) ≫ (eqToHom h).app (L₁.obj X) := by
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app_comp, homEquiv_eq_rec,
      Adjunction.comp_homEquiv]
    simp only [Equiv.trans_apply]
    congr 1
    rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply, adj₁.unit_naturality,
      Functor.map_comp, ← Category.assoc, adjG.right_triangle_components, Category.id_comp]
  exact hl.trans hr.symm

/-- Replacing the adjunction on the left-hand side of a mate by another adjunction with the
same right adjoint whiskers the mate by the canonical comparison of the two left adjoints. -/
theorem mateEquiv_symm_congr_left {L₁ L₂ : A ⥤ B} {R : B ⥤ A} {L₃ : E ⥤ F} {R₃ : F ⥤ E}
    (adj₁ : L₁ ⊣ R) (adj₂ : L₂ ⊣ R) (adj₃ : L₃ ⊣ R₃) (β : TwoSquare R H G R₃) :
    (mateEquiv adj₁ adj₃).symm β =
      ((mateEquiv adj₂ adj₃).symm β).whiskerLeft
        (Adjunction.leftAdjointUniq adj₂ adj₁).hom := by
  apply (mateEquiv adj₁ adj₃).injective
  rw [Equiv.apply_symm_apply, CategoryTheory.conjugateEquiv_mateEquiv_vcomp adj₁ adj₂ adj₃,
    Equiv.apply_symm_apply, conjugateEquiv_leftAdjointUniq_hom]
  ext d
  simp [TwoSquare.whiskerTop]

/-- Replacing the adjunction on the right-hand side of a mate by another adjunction with the
same right adjoint whiskers the mate by the canonical comparison of the two left adjoints. -/
theorem mateEquiv_symm_congr_right {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ L₃ : E ⥤ F} {R : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R) (adj₃ : L₃ ⊣ R) (β : TwoSquare R₁ H G R) :
    (mateEquiv adj₁ adj₃).symm β =
      ((mateEquiv adj₁ adj₂).symm β).whiskerRight
        (Adjunction.leftAdjointUniq adj₃ adj₂).hom := by
  apply (mateEquiv adj₁ adj₃).injective
  rw [Equiv.apply_symm_apply, CategoryTheory.mateEquiv_conjugateEquiv_vcomp adj₁ adj₂ adj₃,
    Equiv.apply_symm_apply, conjugateEquiv_leftAdjointUniq_hom]
  ext d
  simp [TwoSquare.whiskerBottom]

/-- Transposing a morphism `L₁ X ⟶ Y` precomposed with the conjugate of a 2-cell `t : R₁ ⟶ R₂`
is the transpose of the morphism itself, postcomposed with `t`. -/
theorem homEquiv_conjugate {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (t : R₁ ⟶ R₂) {X : A} {Y : B} (f : L₁.obj X ⟶ Y) :
    b.homEquiv X Y (((conjugateEquiv a b).symm t).app X ≫ f) =
      a.homEquiv X Y f ≫ t.app Y := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← Category.assoc, ← unit_conjugateEquiv_symm, Category.assoc, ← t.naturality]
  simp only [Category.assoc]

/-- Transposing a morphism `L₁ X ⟶ Y` precomposed with a 2-cell `α : L₂ ⟶ L₁` between the left
adjoints is the transpose of the morphism itself, postcomposed with the conjugate of `α`.  This
is `Stacks.CategoryTheory.homEquiv_conjugate` with the 2-cell given on the left adjoints: a
comparison of two left adjoints is what a caller normally has in hand, and no rewrite turns it
into the `(conjugateEquiv a b).symm t` of that statement. -/
theorem homEquiv_conjugate' {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (α : L₂ ⟶ L₁) {X : A} {Y : B} (f : L₁.obj X ⟶ Y) :
    b.homEquiv X Y (α.app X ≫ f) = a.homEquiv X Y f ≫ (conjugateEquiv a b α).app Y := by
  have h := homEquiv_conjugate a b (conjugateEquiv a b α) f
  rwa [Equiv.symm_apply_apply] at h

/-- The element-level mates correspondence.  For a square of adjunctions `La ⊣ Ra`, `Lb ⊣ Rb`,
`Lc ⊣ Rc`, `Ld ⊣ Rd` and a 2-cell `t : Rb ⋙ Ra ⟶ Rd ⋙ Rc`, transposing a morphism
`f : La X ⟶ Y` down the left-hand side and across differs from transposing it across and down
the right-hand side exactly by the mate of `t`. -/
theorem homEquiv_mate {La : A ⥤ B} {Ra : B ⥤ A} {Lb : B ⥤ F} {Rb : F ⥤ B}
    {Lc : A ⥤ E} {Rc : E ⥤ A} {Ld : E ⥤ F} {Rd : F ⥤ E}
    (a : La ⊣ Ra) (b : Lb ⊣ Rb) (c : Lc ⊣ Rc) (d : Ld ⊣ Rd)
    (t : Rb ⋙ Ra ⟶ Rd ⋙ Rc) {X : A} {Y : B} (f : La.obj X ⟶ Y) :
    d.homEquiv _ _
        (((conjugateEquiv (a.comp b) (c.comp d)).symm t).app X ≫ Lb.map f) =
      Lc.map (a.homEquiv X Y f) ≫
        ((mateEquiv b c).symm (TwoSquare.mk Rb Rd Ra Rc t)).natTrans.app Y := by
  apply (c.homEquiv X _).injective
  show ((d.homEquiv (Lc.obj X) (Lb.obj Y)).trans
    (c.homEquiv X (Rd.obj (Lb.obj Y)))) _ = _
  rw [← congrFun (congrFun (Adjunction.comp_homEquiv c d) X) (Lb.obj Y),
    homEquiv_conjugate (a.comp b) (c.comp d) t (Lb.map f), Adjunction.comp_homEquiv]
  show (a.homEquiv X _) ((b.homEquiv _ _) (Lb.map f)) ≫ t.app (Lb.obj Y) = _
  simp only [Adjunction.homEquiv_unit]
  rw [b.unit_naturality]
  set ψ := a.unit.app X ≫ Ra.map f with hψ
  calc
    _ = ψ ≫ Ra.map (b.unit.app Y) ≫ t.app (Lb.obj Y) := by
      simp only [hψ, Functor.map_comp, Category.assoc]
    _ = ψ ≫ c.unit.app (Ra.obj Y) ≫
        Rc.map (((mateEquiv b c).symm (TwoSquare.mk Rb Rd Ra Rc t)).natTrans.app Y) :=
      congrArg (ψ ≫ ·) (unit_mateEquiv_symm b c (TwoSquare.mk Rb Rd Ra Rc t) Y)
    _ = _ := by
      have hc : ψ ≫ c.unit.app (Ra.obj Y) = c.unit.app X ≫ Rc.map (Lc.map ψ) :=
        c.unit.naturality ψ
      rw [← Category.assoc, hc]
      simp only [Functor.map_comp, Category.assoc]

/-! ### The counit square of a mate -/

section Counit

variable {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : E ⥤ F} {R₂ : F ⥤ E}

/-- **The counit square pins the mate down.** Let
```
      A ⥤ B
    G ↓   ↓ H
      E ⥤ F
```
be a square whose horizontal legs are the left adjoints of `adj₁ : L₁ ⊣ R₁` and
`adj₂ : L₂ ⊣ R₂`, let `α : G ⋙ L₂ ⟶ L₁ ⋙ H` be a 2-cell and let `β : R₁ ⋙ G ⟶ H ⋙ R₂` be a
candidate for its mate. If the counit square
`L₂(β_d) ≫ ε₂ = α_{R₁ d} ≫ H(ε₁ d)` commutes for every `d`, then `β` *is* the mate of `α`.

`CategoryTheory.mateEquiv_counit` is the converse: the mate always satisfies that square. So
the two together say that the counit square is exactly the mate relation, which is how a
comparison morphism constructed by other means is recognized as a mate. The proof is one line:
the adjunct under `adj₂` is injective and turns the two sides of the square into the two sides
of the desired identity.

`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/BaseChangePasting.lean` carries a
`private` copy of this statement, which this declaration is the public form of; that file does
not import this one, so the copy is left where it is rather than deleted. -/
theorem mateEquiv_eq_of_counit (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : TwoSquare G L₁ L₂ H) (β : TwoSquare R₁ H G R₂)
    (h : ∀ d, L₂.map (β.app d) ≫ adj₂.counit.app (H.obj d) =
      α.app (R₁.obj d) ≫ H.map (adj₁.counit.app d)) :
    mateEquiv adj₁ adj₂ α = β := by
  refine TwoSquare.ext _ _ fun d ↦ ?_
  apply (adj₂.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, mateEquiv_counit, h d]

/-- **Invertibility of a counit transfers down a mate.** In the situation of
`Stacks.CategoryTheory.mateEquiv_eq_of_counit`, if the 2-cell `α` is invertible at `R₁ d`, the
mate of `α` is invertible at `d`, and the counit of `adj₂` is invertible at `H d`, then `H` of
the counit of `adj₁` at `d` is invertible.

This is the transfer the localization of a counit needs: the counit over the whole object,
restricted along `H`, is invertible as soon as the counit formed downstairs is, provided the
two comparison 2-cells are. It is `CategoryTheory.mateEquiv_counit` read as a factorization of
`H(ε₁ d)` through three invertible morphisms. -/
theorem isIso_map_counit_of_isIso_mateEquiv_app (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : TwoSquare G L₁ L₂ H) (d : B) [IsIso (α.app (R₁.obj d))]
    [IsIso ((mateEquiv adj₁ adj₂ α).app d)] [IsIso (adj₂.counit.app (H.obj d))] :
    IsIso (H.map (adj₁.counit.app d)) := by
  have : IsIso (α.app (R₁.obj d) ≫ H.map (adj₁.counit.app d)) := by
    rw [← mateEquiv_counit adj₁ adj₂ α d]
    infer_instance
  exact IsIso.of_isIso_comp_left (α.app (R₁.obj d)) (H.map (adj₁.counit.app d))

/-- The companion of `Stacks.CategoryTheory.isIso_map_counit_of_isIso_mateEquiv_app` running the
other way: invertibility of the restricted counit upstairs makes `L₂` of the mate invertible.
Whether the mate itself is then invertible depends on `L₂` reflecting isomorphisms, which is not
assumed here. -/
theorem isIso_map_mateEquiv_app_of_isIso_map_counit (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : TwoSquare G L₁ L₂ H) (d : B) [IsIso (α.app (R₁.obj d))]
    [IsIso (H.map (adj₁.counit.app d))] [IsIso (adj₂.counit.app (H.obj d))] :
    IsIso (L₂.map ((mateEquiv adj₁ adj₂ α).app d)) := by
  have : IsIso (L₂.map ((mateEquiv adj₁ adj₂ α).app d) ≫ adj₂.counit.app (H.obj d)) := by
    rw [mateEquiv_counit adj₁ adj₂ α d]
    infer_instance
  exact IsIso.of_isIso_comp_right (L₂.map ((mateEquiv adj₁ adj₂ α).app d))
    (adj₂.counit.app (H.obj d))

/-- The mate of a 2-cell `α : G ⋙ L₂ ⟶ L₁ ⋙ H` is, at every object, the transpose under the
adjunction `L₂ ⊣ R₂` of the composite of `α` with the counit of `L₁ ⊣ R₁`. -/
theorem mateEquiv_app_eq_homEquiv (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare G L₁ L₂ H)
    (d : B) :
    (mateEquiv adj₁ adj₂ α).app d =
      adj₂.homEquiv _ _ (α.app (R₁.obj d) ≫ H.map (adj₁.counit.app d)) := by
  simp [mateEquiv_apply, Adjunction.homEquiv_unit]

/-- A transpose `η_a ≫ R(φ)` is unchanged when `a` and the target of `φ` are replaced by equal
objects, the morphism `φ` being replaced by a heterogeneously equal one. -/
theorem unit_comp_map_eq_eqToHom (adj : L₁ ⊣ R₁) {a a' : A} {b b' : B} (ha : a = a')
    (hb : b = b') (φ : L₁.obj a ⟶ b) (φ' : L₁.obj a' ⟶ b')
    (hφ : φ ≍ φ') :
    adj.unit.app a ≫ R₁.map φ =
      eqToHom ha ≫ (adj.unit.app a' ≫ R₁.map φ') ≫ eqToHom (congrArg R₁.obj hb.symm) := by
  subst ha hb
  obtain rfl := eq_of_heq hφ
  simp

end Counit

section Lift

variable {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ : Type*} [Category C₁] [Category C₂] [Category C₃]
  [Category C₄] [Category D₁] [Category D₂] [Category D₃] [Category D₄]
  {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ : C₃ ⥤ C₄} {R₂ : C₄ ⥤ C₃} {G : C₁ ⥤ C₃} {H : C₂ ⥤ C₄}
  {L₁' : D₁ ⥤ D₂} {R₁' : D₂ ⥤ D₁} {L₂' : D₃ ⥤ D₄} {R₂' : D₄ ⥤ D₃} {G' : D₁ ⥤ D₃}
  {H' : D₂ ⥤ D₄} {U₁ : C₁ ⥤ D₁} {U₂ : C₂ ⥤ D₂} {U₃ : C₃ ⥤ D₃} {U₄ : C₄ ⥤ D₄}

/-- **Mates are compatible with functors lying over a square of adjunctions.** Let a square of
adjunctions `L₁ ⊣ R₁`, `L₂ ⊣ R₂` with vertical functors `G`, `H` lie over another one
`L₁' ⊣ R₁'`, `L₂' ⊣ R₂'`, `G'`, `H'` through functors `U₁, …, U₄`: the right adjoints and the
vertical functors commute with the `U`'s up to the isomorphisms `eR₁`, `eR₂`, `eG`, `eH`, the left
adjoints up to `φ₁`, `φ₂`, and the units correspond under these. If a 2-cell
`β : R₁ ⋙ G ⟶ H ⋙ R₂` lies over `β' : R₁' ⋙ G' ⟶ H' ⋙ R₂'`, then the mate of `β` lies over the
mate of `β'`, up to the same comparisons.

This is what identifies a base-change map built from adjunctions of sheaves of modules with the
base-change map of the underlying sheaves of sets. -/
theorem map_mateEquiv_symm_app_of_lift (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₁' : L₁' ⊣ R₁')
    (adj₂' : L₂' ⊣ R₂') (β : TwoSquare R₁ H G R₂) (β' : TwoSquare R₁' H' G' R₂')
    (eR₁ : R₁ ⋙ U₁ ≅ U₂ ⋙ R₁') (eR₂ : R₂ ⋙ U₃ ≅ U₄ ⋙ R₂') (eG : G ⋙ U₃ ≅ U₁ ⋙ G')
    (eH : H ⋙ U₄ ≅ U₂ ⋙ H') (φ₁ : L₁ ⋙ U₂ ≅ U₁ ⋙ L₁') (φ₂ : L₂ ⋙ U₄ ≅ U₃ ⋙ L₂')
    (hu₁ : ∀ X, U₁.map (adj₁.unit.app X) ≫ eR₁.hom.app (L₁.obj X) ≫ R₁'.map (φ₁.hom.app X) =
      adj₁'.unit.app (U₁.obj X))
    (hu₂ : ∀ X, U₃.map (adj₂.unit.app X) ≫ eR₂.hom.app (L₂.obj X) ≫ R₂'.map (φ₂.hom.app X) =
      adj₂'.unit.app (U₃.obj X))
    (hβ : ∀ Y, U₃.map (β.app Y) ≫ eR₂.hom.app (H.obj Y) ≫ R₂'.map (eH.hom.app Y) =
      eG.hom.app (R₁.obj Y) ≫ G'.map (eR₁.hom.app Y) ≫ β'.app (U₂.obj Y))
    (X : C₁) :
    U₄.map (((mateEquiv adj₁ adj₂).symm β).app X) ≫ eH.hom.app (L₁.obj X) ≫
        H'.map (φ₁.hom.app X) =
      φ₂.hom.app (G.obj X) ≫ L₂'.map (eG.hom.app X) ≫
        ((mateEquiv adj₁' adj₂').symm β').app (U₁.obj X) := by
  refine (Iso.inv_comp_eq (φ₂.app (G.obj X))).mp ?_
  apply (adj₂'.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.comp_obj, Functor.map_comp, Iso.app_inv]
  have hRHS := adj₂'.unit.naturality_assoc (eG.hom.app X)
    (R₂'.map (((mateEquiv adj₁' adj₂').symm β').app (U₁.obj X)))
  have hm' := unit_mateEquiv_symm adj₁' adj₂' β' (U₁.obj X)
  have hm := unit_mateEquiv_symm adj₁ adj₂ β X
  have hn := eR₂.hom.naturality (((mateEquiv adj₁ adj₂).symm β).app X)
  have hG := eG.hom.naturality (adj₁.unit.app X)
  have hb := NatTrans.naturality (β' : R₁' ⋙ G' ⟶ H' ⋙ R₂') (φ₁.hom.app X)
  simp only [Functor.id_map, Functor.comp_map, Functor.comp_obj,
    Functor.id_obj] at hRHS hm hm' hn hG hb
  rw [← hRHS, ← hm', ← hu₂, Category.assoc, Category.assoc,
    ← R₂'.map_comp_assoc (φ₂.hom.app _), Iso.hom_inv_id_app, R₂'.map_id, Category.id_comp,
    ← reassoc_of% hn, ← U₃.map_comp_assoc, ← hm, U₃.map_comp,
    Category.assoc, reassoc_of% (hβ (L₁.obj X)), reassoc_of% hG, ← hb, ← G'.map_comp_assoc,
    ← G'.map_comp_assoc, Category.assoc, hu₁]

end Lift

end Stacks.CategoryTheory

end
