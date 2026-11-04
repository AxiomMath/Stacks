module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverIso

/-!
# Comparing 2-fibre products of categories over a base

Fix a base category `C`. For categories `A`, `X`, `Y`, `Z` over `C` with structure functors
`pA`, `pX`, `pY`, `pZ` and 1-morphisms `a : A ⥤ Z`, `f : X ⥤ Y`, `g : Z ⥤ Y` over `C`, the
2-fibre product over `C` of Stacks 0040 is `CategoryTheory.TwoFibreProductOver`. This file
proves two comparisons of such products, both as equivalences *over the first factor*, that is
as `StacksRepresentableCFG.EquivalenceOver`s between the first projections:

* cancelling the middle factor of an iterated product, `A ×_Z (Z ×_Y X) ≃ A ×_Y X`, which is
  the over-`C` form of Stacks 02XD; and
* replacing the second factor by an equivalent one: an equivalence `c : X ⥤ X'` over `C`
  together with a vertical comparison of the two 1-morphisms into `Z` induces an equivalence
  `A ×_Z X ≃ A ×_Z X'`, the over-`C` form of Stacks 02XA and 02XB.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.cancelMiddle`, its inverse `cancelMiddleInv`, and the
  unit `cancelMiddleUnit` and counit `cancelMiddleCounit`.
* `CategoryTheory.TwoFibreProductOver.mapSnd`, the functor induced by a 1-morphism of the
  second factor, and the unit `mapSndUnit` and counit `mapSndCounit`.

## Main results

* `CategoryTheory.TwoFibreProductOver.cancelMiddleEquivalenceOver`: the cancellation
  equivalence over the first factor.
* `CategoryTheory.TwoFibreProductOver.mapSndEquivalenceOver`: the equivalence over the first
  factor induced by an equivalence of the second factor.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

attribute [local implicit_reducible] fst snd structureFunctor

section Cancel

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {A : Type u₂} [Category.{v₂} A]
  {X : Type u₃} [Category.{v₃} X] {Y : Type u₄} [Category.{v₄} Y] {Z : Type u₅} [Category.{v₅} Z]
  (pA : A ⥤ 𝒞) (pX : X ⥤ 𝒞) (pY : Y ⥤ 𝒞) (pZ : Z ⥤ 𝒞)
  (a : A ⥤ Z) (f : X ⥤ Y) (g : Z ⥤ Y) (ha : a ⋙ pZ = pA) (hg : g ⋙ pY = pZ)

/-- Forgetting the middle factor of an iterated 2-fibre product
`A ×_Z (Z ×_Y X) ⥤ A ×_Y X`. -/
def cancelMiddle :
    TwoFibreProductOver pA (structureFunctor pZ pX pY g f) pZ a (fst pZ pX pY g f) ⥤
      TwoFibreProductOver pA pX pY (a ⋙ g) f where
  obj R :=
    { base := R.base
      x := R.x
      y := R.y.y
      hx := R.hx
      hy := R.y.hy.trans R.hy
      iso := g.mapIso R.iso ≪≫ R.y.iso
      vertical := by
        have h1 : pY.IsHomLift (𝟙 R.base) (g.map R.iso.hom) := by
          have := R.vertical
          exact Functor.isHomLift_map_of_comp_eq hg (𝟙 R.base) R.iso.hom
        have hbb : R.y.base = R.base := R.hy
        have h2 : pY.IsHomLift (𝟙 R.base) R.y.iso.hom := by
          rw [← hbb]
          exact R.y.vertical
        simpa using IsHomLift.comp pY (𝟙 R.base) (𝟙 R.base) (g.map R.iso.hom) R.y.iso.hom }
  map {R R'} φ :=
    { hbase := φ.hbase
      a := φ.a
      b := φ.b.b
      ha := φ.ha
      hb := isHomLift_b φ.b φ.hbase φ.hb
      w := by
        have hw : a.map φ.a ≫ R'.iso.hom = R.iso.hom ≫ φ.b.a := φ.w
        have h1 : g.map (a.map φ.a) ≫ g.map R'.iso.hom = g.map R.iso.hom ≫ g.map φ.b.a := by
          rw [← g.map_comp, ← g.map_comp, hw]
        have h2 : g.map φ.b.a ≫ R'.y.iso.hom = R.y.iso.hom ≫ f.map φ.b.b := φ.b.w
        change g.map (a.map φ.a) ≫ g.map R'.iso.hom ≫ R'.y.iso.hom
            = (g.map R.iso.hom ≫ R.y.iso.hom) ≫ f.map φ.b.b
        rw [← Category.assoc, h1, Category.assoc, h2, Category.assoc] }
  map_id R := Hom.ext' rfl rfl
  map_comp φ ψ := Hom.ext' rfl rfl

/-- The inverse of `cancelMiddle`: `A ×_Y X ⥤ A ×_Z (Z ×_Y X)`, inserting the middle factor
with the identity comparison. -/
def cancelMiddleInv :
    TwoFibreProductOver pA pX pY (a ⋙ g) f ⥤
      TwoFibreProductOver pA (structureFunctor pZ pX pY g f) pZ a (fst pZ pX pY g f) where
  obj T :=
    { base := T.base
      x := T.x
      y :=
        { base := T.base
          x := a.obj T.x
          y := T.y
          hx := (Functor.congr_obj ha T.x).trans T.hx
          hy := T.hy
          iso := T.iso
          vertical := T.vertical }
      hx := T.hx
      hy := rfl
      iso := Iso.refl _
      vertical := IsHomLift.id ((Functor.congr_obj ha T.x).trans T.hx) }
  map {T T'} φ :=
    { hbase := φ.hbase
      a := φ.a
      b :=
        { hbase := φ.hbase
          a := a.map φ.a
          b := φ.b
          ha := by
            have := φ.ha
            exact Functor.isHomLift_map_of_comp_eq ha φ.hbase φ.a
          hb := φ.hb
          w := φ.w }
      ha := φ.ha
      hb := by
        refine structureFunctor_isHomLift _ φ.hbase ?_
        have := φ.ha
        exact Functor.isHomLift_map_of_comp_eq ha φ.hbase φ.a
      w := by simp }
  map_id T := Hom.ext' rfl (Hom.ext' (a.map_id T.x) rfl)
  map_comp φ ψ := Hom.ext' rfl (Hom.ext' (a.map_comp φ.a ψ.a) rfl)

/-- The counit of the cancellation equivalence: reinserting and then forgetting the middle
factor is the identity up to the comparison isomorphisms. -/
noncomputable def cancelMiddleCounit :
    cancelMiddleInv pA pX pY pZ a f g ha ⋙ cancelMiddle pA pX pY pZ a f g hg ≅
      𝟭 (TwoFibreProductOver pA pX pY (a ⋙ g) f) := by
  refine NatIso.ofComponents (fun T => ?_) (fun {T T'} φ => ?_)
  · refine isoMk (Iso.refl _) (Iso.refl _) ?_ ?_
    · change eqToHom _ ≫ pX.map (𝟙 T.y) ≫ eqToHom _ = eqToHom _ ≫ pA.map (𝟙 T.x) ≫ eqToHom _
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
        Category.id_comp]
      exact eqToHom_comp_eq _ _ _ _
    · change (a ⋙ g).map (𝟙 T.x) ≫ T.iso.hom
          = (g.map (𝟙 (a.obj T.x)) ≫ T.iso.hom) ≫ f.map (𝟙 T.y)
      simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  · refine Hom.ext' ?_ ?_
    · change φ.a ≫ 𝟙 T'.x = 𝟙 T.x ≫ φ.a
      rw [Category.comp_id, Category.id_comp]
    · change φ.b ≫ 𝟙 T'.y = 𝟙 T.y ≫ φ.b
      rw [Category.comp_id, Category.id_comp]

/-- The unit of the cancellation equivalence. -/
noncomputable def cancelMiddleUnit :
    𝟭 (TwoFibreProductOver pA (structureFunctor pZ pX pY g f) pZ a (fst pZ pX pY g f)) ≅
      cancelMiddle pA pX pY pZ a f g hg ⋙ cancelMiddleInv pA pX pY pZ a f g ha := by
  refine NatIso.ofComponents (fun R => ?_) (fun {R R'} φ => ?_)
  · have hv := R.vertical
    have hvi : pZ.IsHomLift (𝟙 R.base) R.iso.inv := inferInstance
    have hy1 : pX.obj R.y.y = R.base := R.y.hy.trans R.hy
    refine isoMkVertical (U := R.base) (Iso.refl R.x)
      (isoMkVertical (U := R.base) R.iso.symm (Iso.refl R.y.y) hvi (IsHomLift.id hy1) ?_)
      (IsHomLift.id R.hx) ?_ ?_
    · change g.map R.iso.inv ≫ g.map R.iso.hom ≫ R.y.iso.hom = R.y.iso.hom ≫ f.map (𝟙 R.y.y)
      rw [← Category.assoc, ← g.map_comp, R.iso.inv_hom_id, CategoryTheory.Functor.map_id,
        CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    · exact structureFunctor_isHomLift _ (𝟙 R.base) hvi
    · change a.map (𝟙 R.x) ≫ 𝟙 (a.obj R.x) = R.iso.hom ≫ R.iso.inv
      rw [CategoryTheory.Functor.map_id, Category.id_comp, R.iso.hom_inv_id]
  · have hw : a.map φ.a ≫ R'.iso.hom = R.iso.hom ≫ φ.b.a := φ.w
    refine Hom.ext' ?_ ?_
    · change φ.a ≫ 𝟙 R'.x = 𝟙 R.x ≫ φ.a
      rw [Category.comp_id, Category.id_comp]
    · refine Hom.ext' ?_ ?_
      · change φ.b.a ≫ R'.iso.inv = R.iso.inv ≫ a.map φ.a
        refine (Iso.eq_inv_comp R.iso).2 ?_
        rw [← Category.assoc, ← hw, Category.assoc, R'.iso.hom_inv_id, Category.comp_id]
      · change φ.b.b ≫ 𝟙 R'.y.y = 𝟙 R.y.y ≫ φ.b.b
        rw [Category.comp_id, Category.id_comp]

/-- **Cancellation of the middle factor.** The first projection of `A ×_Z (Z ×_Y X)` and the
first projection of `A ×_Y X` are equivalent as categories over `A`. -/
noncomputable def cancelMiddleEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver
      (fst pA (structureFunctor pZ pX pY g f) pZ a (fst pZ pX pY g f))
      (fst pA pX pY (a ⋙ g) f) where
  hom := ⟨cancelMiddle pA pX pY pZ a f g hg, rfl⟩
  inv := ⟨cancelMiddleInv pA pX pY pZ a f g ha, rfl⟩
  unitIso := cancelMiddleUnit pA pX pY pZ a f g ha hg
  counitIso := cancelMiddleCounit pA pX pY pZ a f g ha hg
  unit_over := by
    refine StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ (fun R => ?_)
    refine IsHomLift.of_fac' _ _ _ rfl rfl ?_
    change 𝟙 R.x = eqToHom rfl ≫ 𝟙 R.x ≫ eqToHom rfl
    simp
  counit_over := by
    refine StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ (fun T => ?_)
    refine IsHomLift.of_fac' _ _ _ rfl rfl ?_
    change 𝟙 T.x = eqToHom rfl ≫ 𝟙 T.x ≫ eqToHom rfl
    simp

end Cancel
section MapSnd

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {A : Type u₂} [Category.{v₂} A]
  {W : Type u₃} [Category.{v₃} W] {Q : Type u₄} [Category.{v₄} Q] {Z : Type u₅} [Category.{v₅} Z]
  (pA : A ⥤ 𝒞) (pW : W ⥤ 𝒞) (pQ : Q ⥤ 𝒞) (pZ : Z ⥤ 𝒞)
  (y : A ⥤ Z) (Fw : W ⥤ Z) (Fq : Q ⥤ Z)
  (c : W ⥤ Q) (hc : c ⋙ pQ = pW) (γ : Fw ≅ c ⋙ Fq)
  (hγ : ∀ w, pZ.IsHomLift (𝟙 (pW.obj w)) (γ.hom.app w))

/-- The functor induced on 2-fibre products over the base by a 1-morphism `c` of the second
factor together with a vertical comparison isomorphism `γ`. -/
def mapSnd : TwoFibreProductOver pA pW pZ y Fw ⥤ TwoFibreProductOver pA pQ pZ y Fq where
  obj R :=
    { base := R.base
      x := R.x
      y := c.obj R.y
      hx := R.hx
      hy := (Functor.congr_obj hc R.y).trans R.hy
      iso := R.iso ≪≫ γ.app R.y
      vertical := by
        have h1 := R.vertical
        have h2 : pZ.IsHomLift (𝟙 R.base) (γ.hom.app R.y) := by
          rw [← R.hy]
          exact hγ R.y
        simpa using IsHomLift.comp pZ (𝟙 R.base) (𝟙 R.base) R.iso.hom (γ.hom.app R.y) }
  map {R R'} φ :=
    { hbase := φ.hbase
      a := φ.a
      b := c.map φ.b
      ha := φ.ha
      hb := by
        have := φ.hb
        exact Functor.isHomLift_map_of_comp_eq hc φ.hbase φ.b
      w := by
        have hw : y.map φ.a ≫ R'.iso.hom = R.iso.hom ≫ Fw.map φ.b := φ.w
        have hnat : Fw.map φ.b ≫ γ.hom.app R'.y = γ.hom.app R.y ≫ Fq.map (c.map φ.b) :=
          γ.hom.naturality φ.b
        change y.map φ.a ≫ R'.iso.hom ≫ γ.hom.app R'.y
            = (R.iso.hom ≫ γ.hom.app R.y) ≫ Fq.map (c.map φ.b)
        rw [← Category.assoc, hw, Category.assoc, hnat, Category.assoc] }
  map_id R := Hom.ext' rfl (c.map_id R.y)
  map_comp φ ψ := Hom.ext' rfl (c.map_comp φ.b ψ.b)

end MapSnd
section MapSndEquiv

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {A : Type u₂} [Category.{v₂} A]
  {W : Type u₃} [Category.{v₃} W] {Q : Type u₄} [Category.{v₄} Q] {Z : Type u₅} [Category.{v₅} Z]
  (pA : A ⥤ 𝒞) (pW : W ⥤ 𝒞) (pQ : Q ⥤ 𝒞) (pZ : Z ⥤ 𝒞)
  (y : A ⥤ Z) (Fw : W ⥤ Z) (Fq : Q ⥤ Z)
  (c : W ⥤ Q) (hc : c ⋙ pQ = pW) (γ : Fw ≅ c ⋙ Fq)
  (hγ : ∀ w, pZ.IsHomLift (𝟙 (pW.obj w)) (γ.hom.app w))
  (d : Q ⥤ W) (hd : d ⋙ pW = pQ) (δ : Fq ≅ d ⋙ Fw)
  (hδ : ∀ q, pZ.IsHomLift (𝟙 (pQ.obj q)) (δ.hom.app q))

/-- The unit of the equivalence of 2-fibre products induced by an equivalence of the second
factor. -/
noncomputable def mapSndUnit (ε : c ⋙ d ≅ 𝟭 W)
    (hε : ∀ w, pW.IsHomLift (𝟙 (pW.obj w)) (ε.hom.app w))
    (hcomp : ∀ w, (γ.hom.app w ≫ δ.hom.app (c.obj w)) ≫ Fw.map (ε.hom.app w) =
      𝟙 (Fw.obj w)) :
    𝟭 (TwoFibreProductOver pA pW pZ y Fw) ≅
      mapSnd pA pW pQ pZ y Fw Fq c hc γ hγ ⋙ mapSnd pA pQ pW pZ y Fq Fw d hd δ hδ := by
  have hγδ : ∀ w, γ.hom.app w ≫ δ.hom.app (c.obj w) = Fw.map (ε.inv.app w) := fun w =>
    (Iso.comp_hom_eq_id (Fw.mapIso (ε.app w))).1 (hcomp w)
  refine NatIso.ofComponents (fun R => ?_) (fun {R R'} φ => ?_)
  · have h1 : pW.IsHomLift (𝟙 R.base) (ε.app R.y).hom := by
      rw [← R.hy]
      exact hε R.y
    have h2 := IsHomLift.lift_id_inv pW R.base (ε.app R.y)
    refine isoMkVertical (U := R.base) (Iso.refl R.x) (ε.app R.y).symm (IsHomLift.id R.hx) h2 ?_
    change y.map (𝟙 R.x) ≫ (R.iso.hom ≫ γ.hom.app R.y) ≫ δ.hom.app (c.obj R.y)
        = R.iso.hom ≫ Fw.map (ε.inv.app R.y)
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc, hγδ R.y]
  · refine Hom.ext' ?_ ?_
    · change φ.a ≫ 𝟙 R'.x = 𝟙 R.x ≫ φ.a
      rw [Category.comp_id, Category.id_comp]
    · exact ε.inv.naturality φ.b

/-- The counit of the equivalence of 2-fibre products induced by an equivalence of the second
factor. -/
noncomputable def mapSndCounit (η : d ⋙ c ≅ 𝟭 Q)
    (hη : ∀ q, pQ.IsHomLift (𝟙 (pQ.obj q)) (η.hom.app q))
    (hcomp : ∀ q, (δ.hom.app q ≫ γ.hom.app (d.obj q)) ≫ Fq.map (η.hom.app q) =
      𝟙 (Fq.obj q)) :
    mapSnd pA pQ pW pZ y Fq Fw d hd δ hδ ⋙ mapSnd pA pW pQ pZ y Fw Fq c hc γ hγ ≅
      𝟭 (TwoFibreProductOver pA pQ pZ y Fq) := by
  refine NatIso.ofComponents (fun T => ?_) (fun {T T'} φ => ?_)
  · have h1 : pQ.IsHomLift (𝟙 T.base) (η.app T.y).hom := by
      rw [← T.hy]
      exact hη T.y
    refine isoMkVertical (U := T.base) (Iso.refl T.x) (η.app T.y) (IsHomLift.id T.hx) h1 ?_
    change y.map (𝟙 T.x) ≫ T.iso.hom
        = ((T.iso.hom ≫ δ.hom.app T.y) ≫ γ.hom.app (d.obj T.y)) ≫ Fq.map (η.hom.app T.y)
    rw [CategoryTheory.Functor.map_id, Category.id_comp,
      Category.assoc T.iso.hom (δ.hom.app T.y) (γ.hom.app (d.obj T.y)),
      Category.assoc T.iso.hom (δ.hom.app T.y ≫ γ.hom.app (d.obj T.y))
        (Fq.map (η.hom.app T.y)), hcomp T.y, Category.comp_id]
  · refine Hom.ext' ?_ ?_
    · change φ.a ≫ 𝟙 T'.x = 𝟙 T.x ≫ φ.a
      rw [Category.comp_id, Category.id_comp]
    · exact η.hom.naturality φ.b

/-- The first component of the unit of `mapSndEquivalenceOver` is an identity. -/
@[simp] theorem mapSndUnit_hom_app_a (ε : c ⋙ d ≅ 𝟭 W)
    (hε : ∀ w, pW.IsHomLift (𝟙 (pW.obj w)) (ε.hom.app w))
    (hcomp : ∀ w, (γ.hom.app w ≫ δ.hom.app (c.obj w)) ≫ Fw.map (ε.hom.app w) = 𝟙 (Fw.obj w))
    (R : TwoFibreProductOver pA pW pZ y Fw) :
    ((mapSndUnit pA pW pQ pZ y Fw Fq c hc γ hγ d hd δ hδ ε hε hcomp).hom.app R).a = 𝟙 R.x :=
  rfl

/-- The first component of the counit of `mapSndEquivalenceOver` is an identity. -/
@[simp] theorem mapSndCounit_hom_app_a (η : d ⋙ c ≅ 𝟭 Q)
    (hη : ∀ q, pQ.IsHomLift (𝟙 (pQ.obj q)) (η.hom.app q))
    (hcomp : ∀ q, (δ.hom.app q ≫ γ.hom.app (d.obj q)) ≫ Fq.map (η.hom.app q) = 𝟙 (Fq.obj q))
    (T : TwoFibreProductOver pA pQ pZ y Fq) :
    ((mapSndCounit pA pW pQ pZ y Fw Fq c hc γ hγ d hd δ hδ η hη hcomp).hom.app T).a = 𝟙 T.x :=
  rfl

/-- An equivalence of the second factor of a 2-fibre product over the base induces an
equivalence of the first projections, over the first factor. -/
noncomputable def mapSndEquivalenceOver (ε : c ⋙ d ≅ 𝟭 W) (η : d ⋙ c ≅ 𝟭 Q)
    (hε : ∀ w, pW.IsHomLift (𝟙 (pW.obj w)) (ε.hom.app w))
    (hη : ∀ q, pQ.IsHomLift (𝟙 (pQ.obj q)) (η.hom.app q))
    (hcomp₁ : ∀ w, (γ.hom.app w ≫ δ.hom.app (c.obj w)) ≫ Fw.map (ε.hom.app w) =
      𝟙 (Fw.obj w))
    (hcomp₂ : ∀ q, (δ.hom.app q ≫ γ.hom.app (d.obj q)) ≫ Fq.map (η.hom.app q) =
      𝟙 (Fq.obj q)) :
    StacksRepresentableCFG.EquivalenceOver (fst pA pW pZ y Fw) (fst pA pQ pZ y Fq) where
  hom := ⟨mapSnd pA pW pQ pZ y Fw Fq c hc γ hγ, rfl⟩
  inv := ⟨mapSnd pA pQ pW pZ y Fq Fw d hd δ hδ, rfl⟩
  unitIso := mapSndUnit pA pW pQ pZ y Fw Fq c hc γ hγ d hd δ hδ ε hε hcomp₁
  counitIso := mapSndCounit pA pW pQ pZ y Fw Fq c hc γ hγ d hd δ hδ η hη hcomp₂
  unit_over := by
    refine StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ (fun R => ?_)
    refine IsHomLift.of_fac' _ _ _ rfl rfl ?_
    simp only [Category.id_comp, eqToHom_trans]
    exact (eqToHom_refl _ _).symm
  counit_over := by
    refine StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ (fun T => ?_)
    refine IsHomLift.of_fac' _ _ _ rfl rfl ?_
    simp only [Category.id_comp, eqToHom_trans]
    exact (eqToHom_refl _ _).symm

end MapSndEquiv

end CategoryTheory.TwoFibreProductOver

end
