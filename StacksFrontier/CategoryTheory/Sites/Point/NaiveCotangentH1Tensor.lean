module

public import StacksFrontier.CategoryTheory.Sites.Point.TensorGerms
public import StacksFrontier.RingTheory.NaiveCotangent.FilteredColimitH1
public import StacksFrontier.RingTheory.NaiveCotangent.H1IndEtaleSquare
public import StacksFrontier.RingTheory.NaiveCotangent.SquareMap

/-!
# `H₁` of a chart ring spread over a site, at a point

Let `a : A ⟶ B` be a morphism of presheaves of commutative rings on a category `C`, let
`R → Γ` be a ring map, and let `ρ_X : R → A(X)` and `ε_X : Γ → B(X)` be ring maps compatible
with restriction and with `a`.  (The typical example: `C` is a site localized at a chart
`V = Spec Γ` of a morphism of spaces with a chart `Spec R` of the base, `A` is the inverse image
of the structure sheaf of the base and `B` the structure sheaf.)  Write `H = H₁(L_{Γ/R})`.  The
squares `R → A(X)`, `Γ → B(X)` give maps `H ⟶ H₁(L_{B(X)/A(X)})` and their linear extensions

`τ_X : B(X) ⊗_Γ H ⟶ H₁(L_{B(X)/A(X)})`.

This file proves, for a point `Φ` of a topology on `C` at which the fibres `R → A_Φ` and
`Γ → B_Φ` are filtered colimits of étale algebras, that `τ` is *surjective near `Φ`*: every
element of `H₁(L_{B(X)/A(X)})` lies, after restriction to some neighbourhood of any given lift
of `Φ` to `X`, in the image of `τ`.  At the point, `τ` becomes the base change map of
Stacks 0D08 between filtered colimits of étale algebras, which is bijective; the passage back to
neighbourhoods uses that `H₁` of the naive cotangent complex and tensor products commute with
the filtered colimits defining the fibres.

This is the site-general form of the local surjectivity of the chart comparison in the proof of
Stacks 0D0Y; points detecting coverings, it gives local surjectivity of `τ` on the site.

## Main definitions

* `Stacks.NaiveCotangent.H1Tensor.h1Map`: the map `H ⟶ H₁(L_{B(X)/A(X)})`.
* `Stacks.NaiveCotangent.H1Tensor.h1Tensor`: its linear extension `τ_X`.
* `Stacks.NaiveCotangent.H1Tensor.h1Restrict`: restriction of `H₁(L_{B(X)/A(X)})`.
* `Stacks.NaiveCotangent.H1Tensor.liftSieve`: the arrows along which a class restricts into the
  image of `τ`.

## Main results

* `Stacks.NaiveCotangent.H1Tensor.h1Tensor_restrict`: `τ` commutes with restriction.
* `Stacks.NaiveCotangent.H1Tensor.stalkBaseChange_bijective`: Stacks 0D08 at the point.
* `Stacks.NaiveCotangent.H1Tensor.exists_h1Tensor_eq_h1Restrict`: surjectivity of `τ` near the
  point.

## References

* [Stacks Project, Tag 0D08](https://stacks.math.columbia.edu/tag/0D08)
* [Stacks Project, Tag 0D0Y](https://stacks.math.columbia.edu/tag/0D0Y)
* [Stacks Project, Tag 0D0X](https://stacks.math.columbia.edu/tag/0D0X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite Algebra
  TensorProduct

universe w v u

namespace Stacks.NaiveCotangent.H1Tensor

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] (A B : Cᵒᵖ ⥤ CommRingCat.{w})
  (a : A ⟶ B)
  (R Γ : Type w) [CommRing R] [CommRing Γ] [Algebra R Γ]
  (ρ : ∀ X : C, R →+* ToType (A.obj (op X)))
  (hρ : ∀ {X Y : C} (g : Y ⟶ X) (r : R), A.map g.op (ρ X r) = ρ Y r)
  (ε : ∀ X : C, Γ →+* ToType (B.obj (op X)))
  (hε : ∀ {X Y : C} (g : Y ⟶ X) (γ : Γ), B.map g.op (ε X γ) = ε Y γ)
  (hsq : ∀ (X : C) (r : R), ε X (algebraMap R Γ r) = a.app (op X) (ρ X r))

/-- The algebra structure of `B(X)` over `A(X)` given by `a`. -/
abbrev algX (X : C) : Algebra (ToType (A.obj (op X))) (ToType (B.obj (op X))) :=
  (a.app (op X)).hom.toAlgebra

/-- `H₁(L_{B(X)/A(X)})`. -/
abbrev H1X (X : C) : Type w :=
  @H1Cotangent (ToType (A.obj (op X))) (ToType (B.obj (op X))) _ _ (algX A B a X)

/-- Pasting two squares on `H₁` agrees with any square whose edges are the composed edges. -/
private theorem h1CotangentMapOfSquare_comp_eq {R S R' S' R'' S'' : Type*} [CommRing R]
    [CommRing S] [CommRing R'] [CommRing S'] [CommRing R''] [CommRing S''] [Algebra R S]
    [Algebra R' S'] [Algebra R'' S''] {fR : R →+* R'} {fS : S →+* S'} {gR : R' →+* R''}
    {gS : S' →+* S''} {fR'' : R →+* R''} {fS'' : S →+* S''}
    (h : ∀ r, fS (algebraMap R S r) = algebraMap R' S' (fR r))
    (h' : ∀ r, gS (algebraMap R' S' r) = algebraMap R'' S'' (gR r))
    (h'' : ∀ r, fS'' (algebraMap R S r) = algebraMap R'' S'' (fR'' r))
    (eR : gR.comp fR = fR'') (eS : gS.comp fS = fS'') (x : H1Cotangent R S) :
    NaiveCotangent.h1CotangentMapOfSquare gR gS h'
        (NaiveCotangent.h1CotangentMapOfSquare fR fS h x) =
      NaiveCotangent.h1CotangentMapOfSquare fR'' fS'' h'' x :=
  (NaiveCotangent.h1CotangentMapOfSquare_comp _ _ _ _ _ _ x).trans
    (NaiveCotangent.h1CotangentMapOfSquare_congr _ _ eR eS x)

omit [LocallySmall.{w} C] in
/-- The square of a restriction map commutes. -/
theorem restrictSquare_comm {X Y : C} (g : Y ⟶ X) (r : ToType (A.obj (op X))) :
    (B.map g.op).hom (@algebraMap _ _ _ _ (algX A B a X) r) =
      @algebraMap _ _ _ _ (algX A B a Y) ((A.map g.op).hom r) :=
  (ConcreteCategory.congr_hom (a.naturality g.op) r).symm

/-- **Restriction of `H₁(L_{B(X)/A(X)})`** along `g : Y ⟶ X`. -/
abbrev h1Restrict {X Y : C} (g : Y ⟶ X) : H1X A B a X →+ H1X A B a Y :=
  @NaiveCotangent.h1CotangentMapOfSquare _ _ _ _ _ _ _ _ (algX A B a X) (algX A B a Y)
    (A.map g.op).hom (B.map g.op).hom (restrictSquare_comm A B a g)

omit [LocallySmall.{w} C] in
/-- Restriction of `H₁(L_{B(X)/A(X)})` along a composite is the composite of the restrictions. -/
theorem h1Restrict_comp {X Y Z : C} (g : Y ⟶ X) (k : Z ⟶ Y) (z : H1X A B a X) :
    h1Restrict A B a (k ≫ g) z = h1Restrict A B a k (h1Restrict A B a g z) := by
  let := algX A B a X
  let := algX A B a Y
  let := algX A B a Z
  exact (h1CotangentMapOfSquare_comp_eq _ _ _
    (by rw [op_comp, A.map_comp]; rfl) (by rw [op_comp, B.map_comp]; rfl) z).symm

include hsq in
omit [LocallySmall.{w} C] in
/-- The square `R → A(X)`, `Γ → B(X)` commutes. -/
theorem chartSquare_comm (X : C) (r : R) :
    ε X (algebraMap R Γ r) = @algebraMap _ _ _ _ (algX A B a X) (ρ X r) :=
  hsq X r

/-- **The map `H ⟶ H₁(L_{B(X)/A(X)})`** of the square. -/
abbrev h1Map (X : C) : H1Cotangent R Γ →+ H1X A B a X :=
  @NaiveCotangent.h1CotangentMapOfSquare _ _ _ _ _ _ _ _ _ (algX A B a X) (ρ X) (ε X)
    (chartSquare_comm A B a R Γ ρ ε hsq X)

include hρ hε in
omit [LocallySmall.{w} C] in
/-- The maps `H ⟶ H₁(L_{B(X)/A(X)})` commute with restriction. -/
theorem h1Map_restrict {X Y : C} (g : Y ⟶ X) (h : H1Cotangent R Γ) :
    h1Restrict A B a g (h1Map A B a R Γ ρ ε hsq X h) = h1Map A B a R Γ ρ ε hsq Y h := by
  let := algX A B a X
  let := algX A B a Y
  exact h1CotangentMapOfSquare_comp_eq _ _ _
    (RingHom.ext fun r => hρ g r) (RingHom.ext fun γ => hε g γ) h

/-- `B(X)` as a `Γ`-algebra through `ε`. -/
abbrev algΓ (X : C) : Algebra Γ (ToType (B.obj (op X))) := (ε X).toAlgebra

/-- **`τ_X : B(X) ⊗_Γ H ⟶ H₁(L_{B(X)/A(X)})`.** -/
def h1Tensor (X : C) :
    letI := algΓ B Γ ε X
    ToType (B.obj (op X)) ⊗[Γ] H1Cotangent R Γ →+ H1X A B a X :=
  letI := algΓ B Γ ε X
  letI := algX A B a X
  TensorProduct.liftAddHom
    { toFun := fun s =>
        { toFun := fun h => s • h1Map A B a R Γ ρ ε hsq X h
          map_zero' := by rw [map_zero, smul_zero]
          map_add' := fun h₁ h₂ => by rw [map_add, smul_add] }
      map_zero' := AddMonoidHom.ext fun h =>
        zero_smul (ToType (B.obj (op X))) (h1Map A B a R Γ ρ ε hsq X h)
      map_add' := fun s₁ s₂ => AddMonoidHom.ext fun h => add_smul s₁ s₂ _ }
    (fun γ s h => by
      change (ε X γ * s) • h1Map A B a R Γ ρ ε hsq X h = s • h1Map A B a R Γ ρ ε hsq X (γ • h)
      rw [NaiveCotangent.h1CotangentMapOfSquare_smul, smul_smul, mul_comm])

omit [LocallySmall.{w} C] in
/-- `τ_X (s ⊗ h) = s • h1Map X h`. -/
theorem h1Tensor_tmul (X : C) (s : ToType (B.obj (op X))) (h : H1Cotangent R Γ) :
    letI := algΓ B Γ ε X
    letI := algX A B a X
    h1Tensor A B a R Γ ρ ε hsq X (s ⊗ₜ h) = s • h1Map A B a R Γ ρ ε hsq X h :=
  rfl

/-- Restriction of tensors along `g : Y ⟶ X`. -/
abbrev restrictTensor {X Y : C} (g : Y ⟶ X) :=
  Point.restrictTensor B ε hε (H1Cotangent R Γ) g

include hρ in
/-- **`τ` commutes with restriction.** -/
theorem h1Tensor_restrict {X Y : C} (g : Y ⟶ X)
    (t : letI := algΓ B Γ ε X; ToType (B.obj (op X)) ⊗[Γ] H1Cotangent R Γ) :
    h1Tensor A B a R Γ ρ ε hsq Y (restrictTensor B R Γ ε hε g t) =
      h1Restrict A B a g (h1Tensor A B a R Γ ρ ε hsq X t) := by
  let := algΓ B Γ ε X
  let := algΓ B Γ ε Y
  let := algX A B a X
  let := algX A B a Y
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s h =>
    rw [Point.restrictTensor_tmul, h1Tensor_tmul, h1Tensor_tmul]
    refine Eq.trans ?_ (NaiveCotangent.h1CotangentMapOfSquare_smul _ _ _ s _).symm
    exact congrArg (_ • ·) (h1Map_restrict A B a R Γ ρ hρ ε hε hsq g h).symm
  | add x y hx hy => simp only [map_add, hx, hy]

include hρ in
/-- The arrows along which a class of `H₁(L_{B(X)/A(X)})` restricts into the image of `τ`. -/
def liftSieve (X : C) (z : H1X A B a X) : Sieve X where
  arrows Y g := ∃ t, h1Tensor A B a R Γ ρ ε hsq Y t = h1Restrict A B a g z
  downward_closed := by
    rintro Y₁ Y₂ g ⟨t, ht⟩ k
    refine ⟨restrictTensor B R Γ ε hε k t, ?_⟩
    rw [h1Tensor_restrict A B a R Γ ρ hρ ε hε hsq, ht, h1Restrict_comp]

/-! ### At a point -/

section Point

variable {J : GrothendieckTopology C} (Φ : Point.{w} J)
  (ρΦ : R →+* ToType ((Φ.presheafFiber (A := CommRingCat.{w})).obj A))
  (hρΦ : ∀ (X : C) (x : Φ.fiber.obj X) (r : R), Φ.toPresheafFiber X x A (ρ X r) = ρΦ r)
  (εΦ : Γ →+* ToType ((Φ.presheafFiber (A := CommRingCat.{w})).obj B))
  (hεΦ : ∀ (X : C) (x : Φ.fiber.obj X) (γ : Γ), Φ.toPresheafFiber X x B (ε X γ) = εΦ γ)

/-- The algebra structure of the fibre of `B` over the fibre of `A`. -/
abbrev algΦ :
    Algebra (ToType ((Φ.presheafFiber (A := CommRingCat.{w})).obj A))
      (ToType ((Φ.presheafFiber (A := CommRingCat.{w})).obj B)) :=
  ((Φ.presheafFiber (A := CommRingCat.{w})).map a).hom.toAlgebra

/-- `H₁` of the fibres. -/
abbrev H1Φ : Type w :=
  @H1Cotangent (ToType ((Φ.presheafFiber (A := CommRingCat.{w})).obj A))
    (ToType ((Φ.presheafFiber (A := CommRingCat.{w})).obj B)) _ _ (algΦ A B a Φ)

include hsq hρΦ hεΦ in
omit [LocallySmall.{w} C] in
/-- The square `R → A_Φ`, `Γ → B_Φ` of the fibres commutes. -/
theorem stalkSquare_comm (X : C) (x : Φ.fiber.obj X) (r : R) :
    εΦ (algebraMap R Γ r) = @algebraMap _ _ _ _ (algΦ A B a Φ) (ρΦ r) := by
  rw [← hεΦ X x, ← hρΦ X x, hsq X r]
  exact (Point.toPresheafFiber_naturality_apply Φ a X x _).symm

/-- **The germ map on `H₁`** at a lift `x` of the point to `X`. -/
abbrev germH1 (X : C) (x : Φ.fiber.obj X) : H1X A B a X →+ H1Φ A B a Φ :=
  @NaiveCotangent.h1CotangentMapOfSquare _ _ _ _ _ _ _ _ (algX A B a X) (algΦ A B a Φ)
    (Φ.toPresheafFiber X x A).hom (Φ.toPresheafFiber X x B).hom
    (fun r => (Point.toPresheafFiber_naturality_apply Φ a X x r).symm)

/-- **The map `H ⟶ H₁` of the fibres** at the point. -/
abbrev stalkH1Map (X : C) (x : Φ.fiber.obj X) : H1Cotangent R Γ →+ H1Φ A B a Φ :=
  @NaiveCotangent.h1CotangentMapOfSquare _ _ _ _ _ _ _ _ _ (algΦ A B a Φ) ρΦ εΦ
    (stalkSquare_comm A B a R Γ ρ ε hsq Φ ρΦ hρΦ εΦ hεΦ X x)

omit [LocallySmall.{w} C] in
/-- The germ of the image of `h` under `h1Map X` is its image under `stalkH1Map`. -/
theorem germH1_h1Map (X : C) (x : Φ.fiber.obj X) (h : H1Cotangent R Γ) :
    germH1 A B a Φ X x (h1Map A B a R Γ ρ ε hsq X h) =
      stalkH1Map A B a R Γ ρ ε hsq Φ ρΦ hρΦ εΦ hεΦ X x h := by
  let := algX A B a X
  let := algΦ A B a Φ
  exact h1CotangentMapOfSquare_comp_eq _ _ _
    (RingHom.ext fun r => hρΦ X x r) (RingHom.ext fun γ => hεΦ X x γ) h

omit [LocallySmall.{w} C] in
/-- The germ at `y` of the restriction along `g` is the germ at the image of `y` in `X`. -/
theorem germH1_restrict {X Y : C} (g : Y ⟶ X) (y : Φ.fiber.obj Y) (z : H1X A B a X) :
    germH1 A B a Φ Y y (h1Restrict A B a g z) = germH1 A B a Φ X (Φ.fiber.map g y) z := by
  let := algX A B a X
  let := algX A B a Y
  let := algΦ A B a Φ
  exact h1CotangentMapOfSquare_comp_eq _ _ _
    (RingHom.ext fun r => Point.toPresheafFiber_w_apply Φ g y A r)
    (RingHom.ext fun r => Point.toPresheafFiber_w_apply Φ g y B r) z

/-- **The base change map at the point**, `B_Φ ⊗_Γ H ⟶ H₁(L_{B_Φ/A_Φ})`. -/
def stalkBaseChange (X : C) (x : Φ.fiber.obj X) :
    letI := εΦ.toAlgebra
    ToType ((Φ.presheafFiber (A := CommRingCat.{w})).obj B) ⊗[Γ] H1Cotangent R Γ →+
      H1Φ A B a Φ :=
  letI := εΦ.toAlgebra
  letI := algΦ A B a Φ
  TensorProduct.liftAddHom
    { toFun := fun s =>
        { toFun := fun h => s • stalkH1Map A B a R Γ ρ ε hsq Φ ρΦ hρΦ εΦ hεΦ X x h
          map_zero' := by rw [map_zero, smul_zero]
          map_add' := fun h₁ h₂ => by rw [map_add, smul_add] }
      map_zero' := AddMonoidHom.ext fun h =>
        zero_smul (ToType ((Φ.presheafFiber (A := CommRingCat.{w})).obj B))
          (stalkH1Map A B a R Γ ρ ε hsq Φ ρΦ hρΦ εΦ hεΦ X x h)
      map_add' := fun s₁ s₂ => AddMonoidHom.ext fun h => add_smul s₁ s₂ _ }
    (fun γ s h => by
      change (εΦ γ * s) • stalkH1Map A B a R Γ ρ ε hsq Φ ρΦ hρΦ εΦ hεΦ X x h =
        s • stalkH1Map A B a R Γ ρ ε hsq Φ ρΦ hρΦ εΦ hεΦ X x (γ • h)
      rw [NaiveCotangent.h1CotangentMapOfSquare_smul, smul_smul, mul_comm])

omit [LocallySmall.{w} C] in
/-- `stalkBaseChange (s ⊗ h) = s • stalkH1Map h`. -/
theorem stalkBaseChange_tmul (X : C) (x : Φ.fiber.obj X)
    (s : ToType ((Φ.presheafFiber (A := CommRingCat.{w})).obj B)) (h : H1Cotangent R Γ) :
    letI := εΦ.toAlgebra
    letI := algΦ A B a Φ
    stalkBaseChange A B a R Γ ρ ε hsq Φ ρΦ hρΦ εΦ hεΦ X x (s ⊗ₜ h) =
      s • stalkH1Map A B a R Γ ρ ε hsq Φ ρΦ hρΦ εΦ hεΦ X x h :=
  rfl

/-- The germ map on tensors. -/
abbrev germTensor (X : C) (x : Φ.fiber.obj X) :=
  Point.germTensor Φ B ε εΦ hεΦ (H1Cotangent R Γ) X x

/-- **`τ` at the point is the base change map of the point.** -/
theorem germH1_h1Tensor (X : C) (x : Φ.fiber.obj X)
    (t : letI := algΓ B Γ ε X; ToType (B.obj (op X)) ⊗[Γ] H1Cotangent R Γ) :
    germH1 A B a Φ X x (h1Tensor A B a R Γ ρ ε hsq X t) =
      stalkBaseChange A B a R Γ ρ ε hsq Φ ρΦ hρΦ εΦ hεΦ X x
        (germTensor B R Γ ε Φ εΦ hεΦ X x t) := by
  let := algΓ B Γ ε X
  let := algX A B a X
  let := εΦ.toAlgebra
  let := algΦ A B a Φ
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s h =>
    rw [h1Tensor_tmul, Point.germTensor_tmul, stalkBaseChange_tmul]
    refine (NaiveCotangent.h1CotangentMapOfSquare_smul _ _ _ s _).trans ?_
    exact congrArg (_ • ·) (germH1_h1Map A B a R Γ ρ ε hsq Φ ρΦ hρΦ εΦ hεΦ X x h)
  | add p q hp hq => simp only [map_add, hp, hq]

include hsq hρΦ hεΦ in
omit [LocallySmall.{w} C] in
/-- **Stacks 0D08 at the point: the base change map is bijective** once `R → A_Φ` and
`Γ → B_Φ` are filtered colimits of étale algebras. -/
theorem stalkBaseChange_bijective (X : C) (x : Φ.fiber.obj X)
    (hA : letI := ρΦ.toAlgebra
      (CommAlgCat.etale.{w} R).ind.{w}
        (CommAlgCat.of R (ToType ((Φ.presheafFiber (A := CommRingCat.{w})).obj A))))
    (hB : letI := εΦ.toAlgebra
      (CommAlgCat.etale.{w} Γ).ind.{w}
        (CommAlgCat.of Γ (ToType ((Φ.presheafFiber (A := CommRingCat.{w})).obj B)))) :
    Function.Bijective (stalkBaseChange A B a R Γ ρ ε hsq Φ ρΦ hρΦ εΦ hεΦ X x) := by
  let := εΦ.toAlgebra
  let := algΦ A B a Φ
  let := ρΦ.toAlgebra
  let : Algebra R (ToType ((Φ.presheafFiber (A := CommRingCat.{w})).obj B)) :=
    (εΦ.comp (algebraMap R Γ)).toAlgebra
  have : IsScalarTower R Γ (ToType ((Φ.presheafFiber (A := CommRingCat.{w})).obj B)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R (ToType ((Φ.presheafFiber (A := CommRingCat.{w})).obj A))
      (ToType ((Φ.presheafFiber (A := CommRingCat.{w})).obj B)) :=
    IsScalarTower.of_algebraMap_eq fun r =>
      stalkSquare_comm A B a R Γ ρ ε hsq Φ ρΦ hρΦ εΦ hεΦ X x r
  have hbij := Algebra.bijective_h1Cotangent_map_liftBaseChange_of_ind_etale R
    (ToType ((Φ.presheafFiber (A := CommRingCat.{w})).obj A)) Γ
    (ToType ((Φ.presheafFiber (A := CommRingCat.{w})).obj B)) hA hB
  convert hbij using 1
  funext t
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s h =>
    rw [stalkBaseChange_tmul, LinearMap.liftBaseChange_tmul,
      NaiveCotangent.h1Cotangent_map_eq_h1CotangentMapOfSquare]
    rfl
  | add p q hp hq => rw [map_add, map_add, hp, hq]

/-- **A class of `H₁` with vanishing germ vanishes on a smaller neighbourhood.** -/
theorem exists_h1Restrict_eq_zero (X : C) (x : Φ.fiber.obj X) (z : H1X A B a X)
    (hz : germH1 A B a Φ X x z = 0) :
    ∃ (Y : C) (g : Y ⟶ X) (y : Φ.fiber.obj Y), Φ.fiber.map g y = x ∧
      h1Restrict A B a g z = 0 := by
  obtain ⟨j, t, ht⟩ := NaiveCotangent.exists_h1CotangentMapOfSquare_eq_zero_of_isColimit
    (Functor.whiskerLeft (Functor.Elements.π Φ.fiber).op a)
    (colimit.isColimit _) (colimit.isColimit _)
    ((Φ.presheafFiber (A := CommRingCat.{w})).map a)
    (fun i => colimit.ι_desc _ _) (op (Φ.fiber.elementsMk X x)) z hz
  exact ⟨j.unop.obj, t.unop.hom, j.unop.val, t.unop.map_val, ht⟩

include hρ hε hsq hρΦ hεΦ in
/-- **Surjectivity of `τ` near the point**: every class of `H₁(L_{B(X)/A(X)})` lies, on a
neighbourhood of any lift of the point to `X`, in the image of `τ`. -/
theorem exists_h1Tensor_eq_h1Restrict (X : C) (x : Φ.fiber.obj X) (z : H1X A B a X)
    (hA : letI := ρΦ.toAlgebra
      (CommAlgCat.etale.{w} R).ind.{w}
        (CommAlgCat.of R (ToType ((Φ.presheafFiber (A := CommRingCat.{w})).obj A))))
    (hB : letI := εΦ.toAlgebra
      (CommAlgCat.etale.{w} Γ).ind.{w}
        (CommAlgCat.of Γ (ToType ((Φ.presheafFiber (A := CommRingCat.{w})).obj B)))) :
    ∃ (Y : C) (g : Y ⟶ X) (y : Φ.fiber.obj Y), Φ.fiber.map g y = x ∧
      ∃ t : (letI := algΓ B Γ ε Y; ToType (B.obj (op Y)) ⊗[Γ] H1Cotangent R Γ),
        h1Tensor A B a R Γ ρ ε hsq Y t = h1Restrict A B a g z := by
  obtain ⟨ξ, hξ⟩ := (stalkBaseChange_bijective A B a R Γ ρ ε hsq Φ ρΦ hρΦ εΦ hεΦ X x
    hA hB).surjective (germH1 A B a Φ X x z)
  obtain ⟨Y₁, g₁, y₁, hy₁, t₁, ht₁⟩ := Point.exists_germTensor_eq Φ B ε εΦ hεΦ
    (H1Cotangent R Γ) x ξ
  let z₁ := h1Tensor A B a R Γ ρ ε hsq Y₁ t₁ - h1Restrict A B a g₁ z
  have hz₁ : germH1 A B a Φ Y₁ y₁ z₁ = 0 := by
    rwa [map_sub, germH1_h1Tensor A B a R Γ ρ ε hsq Φ ρΦ hρΦ εΦ hεΦ Y₁ y₁ t₁,
      germH1_restrict, hy₁, sub_eq_zero, ht₁]
  obtain ⟨Y₂, g₂, y₂, hy₂, hg₂⟩ :=
    exists_h1Restrict_eq_zero A B a Φ Y₁ y₁ z₁ hz₁
  refine ⟨Y₂, g₂ ≫ g₁, y₂, by rw [Functor.map_comp_apply, hy₂, hy₁],
    restrictTensor B R Γ ε hε g₂ t₁, ?_⟩
  rw [map_sub, sub_eq_zero] at hg₂
  rw [h1Tensor_restrict A B a R Γ ρ hρ ε hε hsq, hg₂, ← h1Restrict_comp]

end Point

end Stacks.NaiveCotangent.H1Tensor

end
