module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.SheafLevelComplexSections
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolution

/-!
# Degree zero of the sheaf-level Čech complex: the augmentation is a kernel

Let `C` be a site with finite products, let `R` be a sheaf of rings on `C`, let `F` be a sheaf of
`R`-modules and let `{U_i → X}` be a family of morphisms whose target `X` is a *terminal* object.
`StacksFrontier/CategoryTheory/Sites/Cohomology/Cech/SheafLevelComplexSections.lean` proves that the
sheaf-level Čech complex `Stacks.CechSite.SheafLevel.complexFunctor` of a family covering `X` is
exact in every positive degree and that its augmentation is a monomorphism.  This file supplies
the remaining half of degree zero — **exactness of `F ⟶ Č⁰ ⟶ Č¹`** — and concludes that the
augmentation `F[0] ⟶ Č(E, F)` is a **quasi-isomorphism**: the Čech complex of a covering of a
terminal object is a resolution of `F`.

## Main definitions

* `Stacks.CechSite.SheafLevel.pairLift`: for an object `W` with a morphism `q : W ⟶ U_{i₀}` and a
  degree-zero index `x`, the morphism `U_x ⨯ W ⟶ U_x ×_X U_{i₀}` of `Over X` cut out by the
  projection to `U_x` and by `q` after the projection to `W`.
* `Stacks.CechSite.SheafLevel.pairDiagonal`: the same morphism paired with the projection to `W`,
  a morphism `U_x ⨯ W ⟶ (U_x ×_X U_{i₀}) ⨯ W` of `C`.  Restriction of sections along it is the
  contracting homotopy of the Čech complex of sections over `W`.
* `Stacks.CechSite.SheafLevel.sectionsRetraction` and
  `Stacks.CechSite.SheafLevel.sectionsHomotopy`: the retraction of the augmentation and the
  contracting homotopy of the Čech complex of sections over `W`.
* `Stacks.CechSite.SheafLevel.isLimitFanSectionsOver`: sections over `W` carry a product of
  sheaves of modules to a product of abelian groups.

## Main results

* `Stacks.CechSite.SheafLevel.d_zero_comp_pi`: the degree-zero differential of the sheaf-level
  Čech complex, composed with a projection, is the difference of the two transition maps.
* `Stacks.CechSite.SheafLevel.exact_sectionsOver_shortComplex`: **over an object `W` admitting a
  morphism to a member of the family, the complex of sections `F(W) ⟶ Γ(W, Č⁰) ⟶ Γ(W, Č¹)` is
  exact.**  Neither a covering hypothesis nor a sheaf condition is used: the contracting homotopy
  is written down.
* `Stacks.CechSite.SheafLevel.exact_shortComplex_augmentation_of_coversTop`: **`F ⟶ Č⁰ ⟶ Č¹` is
  exact for a family covering a terminal object.**
* `Stacks.CechSite.SheafLevel.isLimit_augmentationFork_of_coversTop`: equivalently, the
  augmentation is a kernel of `d⁰`.
* `Stacks.CechSite.SheafLevel.quasiIsoAt_augmentationHom_zero_of_coversTop` and
  `Stacks.CechSite.SheafLevel.quasiIso_augmentationHom_of_coversTop`: **the augmentation
  `F[0] ⟶ Č(E, F)` of the sheaf-level Čech complex of a family covering a terminal object is a
  quasi-isomorphism.**

## Implementation notes

The degree-zero statement is proved by the same locality argument as the two statements of
`SheafLevelComplexSections.lean`: it is enough to produce, over every object `W` admitting a
morphism `q : W ⟶ U_{i₀}` to a member of the family, a preimage of every section of `Č⁰` killed by
`d⁰`.  What is new is that over such a `W` the complex of sections is *contractible* in degree
zero, and the contracting homotopy is written down rather than obtained from a comparison
isomorphism: at the degree-zero index `x` it restricts a section over `(U_x ×_X U_{i₀}) ⨯ W` to
one over `U_x ⨯ W`, using `q` to supply the missing map to `U_{i₀}`.
`CategoryTheory.SimplicialSiteSituation.exact_of_contracting` then gives exactness from the
identity `r ≫ aug + d⁰ ≫ s = 𝟙`, which is checked on each factor of the degree-zero product
through `Stacks.CechSite.SheafLevel.isLimitFanSectionsOver`.

This is route (B) of the two recorded in the implementation notes of
`SheafLevelComplexSections.lean`.  Route (A) — reading
`Stacks.CategoryTheory.CechComplex.isLimitAugmentationFork` through
`Stacks.CechSite.SheafLevel.complexFunctorSectionsIso` — is **not** taken, and the compatibility
it needs remains unproved: nothing below identifies the sections of
`Stacks.CechSite.SheafLevel.augmentation` with `Stacks.Cohomology.CechZero.aug`.  The route taken
here needs no sheaf condition on the coefficients, so
`Stacks.CechSite.SheafLevel.isSheaf_prodRestriction` is not used either; the only input beyond
terminality of `X` is that the family is covering, consumed by the locality criterion
`Stacks.SheafOfModules.ComplexLocality.exact_of_coversTop`.

The degree-zero statements also need **no finite products in the slices `Over W`**, unlike the
positive-degree exactness of `SheafLevelComplexSections.lean`, which base-changes the family to
`Over W`.  That hypothesis therefore appears only from
`Stacks.CechSite.SheafLevel.quasiIsoAt_augmentationHom_of_coversTop` on, where the positive
degrees are brought in.

Two pieces of index bookkeeping are isolated so that each is paid once.  A degree-zero index is a
map `Fin 1 → E.I₀`, and the two faces of a degree-one index `y` are `y ∘ δ₀` and `y ∘ δ₁`, which
for a *variable* argument do not reduce; so every statement below is phrased at a degree-zero
index already of the form `y ∘ δ₁` with `y = Fin.cons i (fun _ ↦ i₀)`, which is no loss because
`Stacks.CechSite.SheafLevel.degreeZeroIndex_eq` puts an arbitrary index in that form.  With that
choice the *other* face `y ∘ δ₀` is the constant index at `i₀` definitionally, since `δ₀ a`
reduces to `a.succ`, so no transport along an equality of indices is needed anywhere.

Those statements are, however, hostile to `rw`: a goal mentioning the degree-zero object at an
index whose type is spelled `Fin 1 → E.I₀` rather than
`((cechSimplicialObject E).obj (op ⦋0⦌)).I` is reported as not type-correct at `implicit`
transparency, because `Stacks.CechSite.cechFormalCoproduct` is not unfolded there.  Every proof
below therefore either is an explicit term or rewrites only inside a goal all of whose objects are
variables; that is why the algebra of the contracting identity is carried out in
`Stacks.CechSite.SheafLevel.comp_pi_of_contracting`, an abstract lemma about a preadditive
category, rather than in place.  This is the same obstruction as the one documented at
`Stacks.CechSite.SheafLevel.starMap_comp_snd`.

## References

* [Stacks Project, Tag 03AT](https://stacks.math.columbia.edu/tag/03AT)
* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.WeaklyContractible (sectionsOver)
open scoped Simplicial

universe w v u

namespace Stacks.CechSite.SheafLevel

/-! ### Abstract lemmas -/

section Abstract

variable {A : Type u} [Category.{v} A]

/-- **Restriction along a composite.**  For a presheaf, the composite of the restriction maps of
`a` and of `b` is the restriction map of `b ≫ a`. -/
theorem presheafMap_op_comp {C : Type*} [Category C] (P : Cᵒᵖ ⥤ A) {Z Y V : C} (a : Y ⟶ Z)
    (b : V ⟶ Y) : P.map a.op ≫ P.map b.op = P.map (b ≫ a).op :=
  (P.map_comp _ _).symm.trans (congrArg P.map op_comp.symm)

variable [Preadditive A]

/-- **An alternating sum of two morphisms, composed with a third.**  The shape in which the
degree-zero Čech differential is given by
`Stacks.CategoryTheory.CechComplex.alternatingCofaceMapComplex_obj_d`. -/
theorem sum_two_zsmul_comp {P Q T : A} (d : Fin 2 → (P ⟶ Q)) (π : Q ⟶ T) :
    (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • d i) ≫ π = d 0 ≫ π - d 1 ≫ π := by
  rw [Fin.sum_univ_two, Preadditive.add_comp, Preadditive.zsmul_comp, Preadditive.zsmul_comp]
  simp [sub_eq_add_neg]

/-- An additive functor carries a difference of composites to the difference of the composites. -/
theorem map_sub_comp_comp {B : Type*} [Category B] [Preadditive B] (G : A ⥤ B) [G.Additive]
    {P Q₀ Q₁ T : A} (a : P ⟶ Q₀) (b : Q₀ ⟶ T) (c : P ⟶ Q₁) (d : Q₁ ⟶ T) :
    G.map (a ≫ b - c ≫ d) = G.map a ≫ G.map b - G.map c ≫ G.map d := by
  rw [G.map_sub, G.map_comp, G.map_comp]

/-- **The contracting identity, on one factor of a product.**  If `r` is a retraction of `f` up to
the comparison `u`, if `s` is, on the factor at hand, minus the restriction `w` of the factor of
`g` at a neighbouring index, if `g` there is the difference of two transition maps `α` and `β`, and
if `β ≫ w` is the identity, then `r ≫ f + g ≫ s` agrees with the identity on that factor.

Stated for abstract objects and morphisms of a preadditive category: this is the algebra of the
degree-zero contracting homotopy of a Čech complex, separated from the identification of its
terms, which is what makes it provable by rewriting. -/
theorem comp_pi_of_contracting {P Q Z A₀ A₁ A₂ : A} (f : Z ⟶ P) (g : P ⟶ Q) (r : P ⟶ Z)
    (s : Q ⟶ P) (π₁ : P ⟶ A₁) (π₂ : Q ⟶ A₂) (c : P ⟶ A₀) (u : Z ⟶ A₁) (α : A₀ ⟶ A₂)
    (β : A₁ ⟶ A₂) (w : A₂ ⟶ A₁) (hf : f ≫ π₁ = u) (hs : s ≫ π₁ = -(π₂ ≫ w))
    (hg : g ≫ π₂ = c ≫ α - π₁ ≫ β) (hr : r ≫ u = c ≫ α ≫ w) (hβ : β ≫ w = 𝟙 A₁) :
    (r ≫ f + g ≫ s) ≫ π₁ = π₁ := by
  have hgw : g ≫ π₂ ≫ w = c ≫ α ≫ w - π₁ ≫ (β ≫ w) := by
    rw [← Category.assoc, hg, Preadditive.sub_comp, Category.assoc, Category.assoc]
  rw [Preadditive.add_comp, Category.assoc, hf, hr, Category.assoc, hs, Preadditive.comp_neg,
    hgw, hβ, Category.comp_id]
  abel

end Abstract

/-! ### The contracting homotopy of the Čech complex of sections over an object -/

section Diagonal

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C] [HasFiniteProducts C]
  {X : C} (E : PreZeroHypercover.{w} X) [HasFiniteProducts (Over X)]

omit [HasBinaryProducts C] [HasFiniteProducts C] [HasFiniteProducts (Over X)] in
/-- **Every degree-zero index is a face of a pair.**  A map `x : Fin 1 → E.I₀` is the composite of
the pair `(x 0, i₀)` with the second face map, for any `i₀`.  This is the form in which the
degree-zero statements below are phrased; see the implementation notes of this file. -/
theorem degreeZeroIndex_eq (i₀ : E.I₀) (x : Fin 1 → E.I₀) :
    ∃ i : E.I₀, x = (Fin.cons i (fun _ ↦ i₀) : Fin 2 → E.I₀) ∘
      (SimplexCategory.δ (1 : Fin 2)).toOrderHom.toFun := by
  refine ⟨x 0, funext fun a ↦ ?_⟩
  rw [Fin.fin_one_eq_zero a]
  rfl

/-- **The diagonal into a degree-one fibre product, as a morphism of `Over X`.**  For a morphism
`q : W ⟶ U_{i₀}` and a degree-zero index `x`, the morphism `U_x ⨯ W ⟶ U_x ×_X U_{i₀}` whose first
component is the projection to `U_x` and whose second is `q` after the projection to `W`.  Both
components are morphisms of `Over X` because `X` is terminal. -/
noncomputable def pairLift (hX : IsTerminal X) {W : C} {i₀ : E.I₀} (q : W ⟶ E.X i₀)
    (x : Fin 1 → E.I₀) :
    Over.mk (hX.from
        ((((cechSimplicialObject E).obj (op (⦋0⦌ : SimplexCategory))).obj x).left ⨯ W)) ⟶
      ((cechSimplicialObject E).obj (op (⦋1⦌ : SimplexCategory))).obj
        (Fin.cons (x 0) (fun _ ↦ i₀)) :=
  Pi.lift (Fin.cons
    (Over.homMk (prod.fst ≫ (Pi.π (fun a : Fin 1 ↦ Over.mk (E.f (x a))) 0).left)
      (hX.hom_ext _ _))
    (fun _ : Fin 1 ↦ Over.homMk (V := Over.mk (E.f i₀)) (prod.snd ≫ q) (hX.hom_ext _ _)))

/-- **The projection to `W`, as a morphism of `Over X`.**  Every morphism of `C` is one of
`Over X` when `X` is terminal; this names the one used below. -/
noncomputable def overSnd (hX : IsTerminal X) (Z W : C) :
    Over.mk (hX.from (Z ⨯ W)) ⟶ Over.mk (hX.from W) :=
  Over.homMk prod.snd (hX.hom_ext _ _)

omit [HasFiniteProducts C] in
/-- The component of `Stacks.CechSite.SheafLevel.pairLift` at the index `0` is the projection to
the degree-zero fibre product followed by its own unique projection. -/
theorem pairLift_comp_pi_zero (hX : IsTerminal X) {W : C} {i₀ : E.I₀} (q : W ⟶ E.X i₀)
    (x : Fin 1 → E.I₀) :
    pairLift E hX q x ≫ Pi.π _ 0 =
      Over.homMk (prod.fst ≫ (Pi.π (fun a : Fin 1 ↦ Over.mk (E.f (x a))) 0).left)
        (hX.hom_ext _ _) :=
  Pi.lift_π _ 0

omit [HasFiniteProducts C] in
/-- The component of `Stacks.CechSite.SheafLevel.pairLift` at a successor index is `q` after the
projection to `W`. -/
theorem pairLift_comp_pi_succ (hX : IsTerminal X) {W : C} {i₀ : E.I₀} (q : W ⟶ E.X i₀)
    (x : Fin 1 → E.I₀) (a : Fin 1) :
    pairLift E hX q x ≫ Pi.π _ a.succ =
      Over.homMk (V := Over.mk (E.f i₀)) (prod.snd ≫ q) (hX.hom_ext _ _) :=
  Pi.lift_π _ a.succ

omit [HasBinaryProducts C] [HasFiniteProducts C] in
/-- **The face maps of the Čech simplicial object are the lifts of the reindexed projections.**
This is the definition of `Stacks.CechSite.cechFormalCoproductMap`, recorded so that the face maps
can be composed with `Stacks.CechSite.SheafLevel.pairLift`. -/
theorem face_eq (k : Fin 2) (y : Fin 2 → E.I₀) :
    ((cechSimplicialObject E).map (SimplexCategory.δ k).op).φ y =
      Pi.lift (fun a : Fin 1 ↦ Pi.π _ ((SimplexCategory.δ k).toOrderHom.toFun a)) := rfl

omit [HasFiniteProducts C] in
/-- **The lift followed by the second face map is the projection.**  The second face of the pair
`(i, i₀)` is the index `i`, and the corresponding morphism of fibre products takes the lift back to
the projection `U_x ⨯ W ⟶ U_x`. -/
theorem pairLift_comp_faceOne (hX : IsTerminal X) {W : C} {i₀ : E.I₀} (q : W ⟶ E.X i₀)
    (i : E.I₀) :
    pairLift E hX q ((Fin.cons i (fun _ ↦ i₀) : Fin 2 → E.I₀) ∘
        (SimplexCategory.δ (1 : Fin 2)).toOrderHom.toFun) ≫
      ((cechSimplicialObject E).map (SimplexCategory.δ (1 : Fin 2)).op).φ
        (Fin.cons i (fun _ ↦ i₀)) =
      Over.homMk prod.fst (hX.hom_ext _ _) := by
  refine (congrArg (fun z ↦ pairLift E hX q _ ≫ z)
    (face_eq E (1 : Fin 2) (Fin.cons i (fun _ ↦ i₀)))).trans (Pi.hom_ext _ _ fun a ↦ ?_)
  obtain rfl : a = 0 := Fin.fin_one_eq_zero a
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦ pairLift E hX q _ ≫ z) (Pi.lift_π _ (0 : Fin 1))).trans
      (pairLift_comp_pi_zero E hX q _))

/-- **The degree-zero diagonal, as a morphism of `Over X`.**  This is the morphism underlying
`Stacks.CechSite.SheafLevel.degreeZeroDiagonal`, which is its image under `Over.forget X`. -/
noncomputable def degreeZeroLift (hX : IsTerminal X) {W : C} {i₀ : E.I₀} (q : W ⟶ E.X i₀) :
    Over.mk (hX.from W) ⟶
      ((cechSimplicialObject E).obj (op (⦋0⦌ : SimplexCategory))).obj (fun _ ↦ i₀) :=
  Pi.lift (fun _ : Fin 1 ↦ Over.homMk (V := Over.mk (E.f i₀)) q (hX.hom_ext _ _))

omit [HasBinaryProducts C] [HasFiniteProducts C] in
/-- The components of `Stacks.CechSite.SheafLevel.degreeZeroLift` are `q`. -/
theorem degreeZeroLift_comp_pi (hX : IsTerminal X) {W : C} {i₀ : E.I₀} (q : W ⟶ E.X i₀)
    (a : Fin 1) :
    degreeZeroLift E hX q ≫ Pi.π _ a =
      Over.homMk (V := Over.mk (E.f i₀)) q (hX.hom_ext _ _) :=
  Pi.lift_π _ a

omit [HasBinaryProducts C] [HasFiniteProducts C] in
/-- The degree-zero diagonal is the image of `Stacks.CechSite.SheafLevel.degreeZeroLift`. -/
theorem degreeZeroLift_left (hX : IsTerminal X) {W : C} {i₀ : E.I₀} (q : W ⟶ E.X i₀) :
    (degreeZeroLift E hX q).left = degreeZeroDiagonal E hX q := rfl

omit [HasFiniteProducts C] in
/-- **The lift followed by the first face map is the degree-zero diagonal after the projection to
`W`.**  The first face of the pair `(i, i₀)` is the constant index `i₀`, definitionally, and the
corresponding morphism of fibre products takes the lift to the lift of `q`, which is
`Stacks.CechSite.SheafLevel.degreeZeroDiagonal`. -/
theorem pairLift_comp_faceZero (hX : IsTerminal X) {W : C} {i₀ : E.I₀} (q : W ⟶ E.X i₀)
    (i : E.I₀) :
    pairLift E hX q ((Fin.cons i (fun _ ↦ i₀) : Fin 2 → E.I₀) ∘
        (SimplexCategory.δ (1 : Fin 2)).toOrderHom.toFun) ≫
      ((cechSimplicialObject E).map (SimplexCategory.δ (0 : Fin 2)).op).φ
        (Fin.cons i (fun _ ↦ i₀)) =
      overSnd hX (((cechSimplicialObject E).obj (op (⦋0⦌ : SimplexCategory))).obj
          ((Fin.cons i (fun _ ↦ i₀) : Fin 2 → E.I₀) ∘
            (SimplexCategory.δ (1 : Fin 2)).toOrderHom.toFun)).left W ≫
        degreeZeroLift E hX q := by
  refine (congrArg (fun z ↦ pairLift E hX q _ ≫ z)
    (face_eq E (0 : Fin 2) (Fin.cons i (fun _ ↦ i₀)))).trans (Pi.hom_ext _ _ fun a ↦ ?_)
  refine (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦ pairLift E hX q _ ≫ z) (Pi.lift_π _ a)).trans ?_)
  refine (pairLift_comp_pi_succ E hX q _ a).trans ?_
  refine ((Category.assoc _ _ _).trans
    (congrArg (fun z ↦ overSnd hX (((cechSimplicialObject E).obj
        (op (⦋0⦌ : SimplexCategory))).obj
        ((Fin.cons i (fun _ ↦ i₀) : Fin 2 → E.I₀) ∘
          (SimplexCategory.δ (1 : Fin 2)).toOrderHom.toFun)).left W ≫ z)
      (degreeZeroLift_comp_pi E hX q a))).symm

/-- **The contracting homotopy, as a morphism of `C`.**  For a morphism `q : W ⟶ U_{i₀}` and a
degree-zero index `x`, the morphism `U_x ⨯ W ⟶ (U_x ×_X U_{i₀}) ⨯ W` cut out by
`Stacks.CechSite.SheafLevel.pairLift` and by the projection to `W`.  Restriction of sections of a
sheaf along it is the degree-zero component of the homotopy. -/
noncomputable def pairDiagonal (hX : IsTerminal X) {W : C} {i₀ : E.I₀} (q : W ⟶ E.X i₀)
    (x : Fin 1 → E.I₀) :
    (((cechSimplicialObject E).obj (op (⦋0⦌ : SimplexCategory))).obj x).left ⨯ W ⟶
      (((cechSimplicialObject E).obj (op (⦋1⦌ : SimplexCategory))).obj
        (Fin.cons (x 0) (fun _ ↦ i₀))).left ⨯ W :=
  prod.lift (pairLift E hX q x).left prod.snd

/-- If `pairLift` followed by `f` is `g`, the homotopy followed by `f ⨯ 𝟙 W` is the lift of `g` and
the projection to `W`. -/
private theorem pairDiagonal_comp_map_of_pairLift_comp {C : Type u} [Category.{v} C]
    [HasBinaryProducts C] {X : C} (E : PreZeroHypercover.{w} X) [HasFiniteProducts (Over X)]
    (hX : IsTerminal X) {W : C} {i₀ : E.I₀}
    (q : W ⟶ E.X i₀) (x : Fin 1 → E.I₀) {T : Over X}
    (f : ((cechSimplicialObject E).obj (op (⦋1⦌ : SimplexCategory))).obj
      (Fin.cons (x 0) (fun _ ↦ i₀)) ⟶ T) (g : _ ⟶ T) (h : pairLift E hX q x ≫ f = g) :
    pairDiagonal E hX q x ≫ prod.map f.left (𝟙 W) = prod.lift g.left prod.snd :=
  (prod.lift_map _ _ _ _).trans
    ((congrArg (fun z ↦ prod.lift z (prod.snd ≫ 𝟙 W))
        ((Over.comp_left ..).symm.trans (congrArg Over.Hom.left h))).trans
      (congrArg (prod.lift _) (Category.comp_id prod.snd)))

omit [HasFiniteProducts C] in
/-- **The homotopy composed with the second transition map is the identity.** -/
theorem pairDiagonal_comp_faceOne (hX : IsTerminal X) {W : C} {i₀ : E.I₀} (q : W ⟶ E.X i₀)
    (i : E.I₀) :
    pairDiagonal E hX q ((Fin.cons i (fun _ ↦ i₀) : Fin 2 → E.I₀) ∘
        (SimplexCategory.δ (1 : Fin 2)).toOrderHom.toFun) ≫
      prod.map (((cechSimplicialObject E).map (SimplexCategory.δ (1 : Fin 2)).op).φ
        (Fin.cons i (fun _ ↦ i₀))).left (𝟙 W) = 𝟙 _ :=
  (pairDiagonal_comp_map_of_pairLift_comp E hX q _ _ _ (pairLift_comp_faceOne E hX q i)).trans
    prod.lift_fst_snd

omit [HasFiniteProducts C] in
/-- **The homotopy composed with the first transition map is the degree-zero diagonal after the
projection to `W`.** -/
theorem pairDiagonal_comp_faceZero (hX : IsTerminal X) {W : C} {i₀ : E.I₀} (q : W ⟶ E.X i₀)
    (i : E.I₀) :
    pairDiagonal E hX q ((Fin.cons i (fun _ ↦ i₀) : Fin 2 → E.I₀) ∘
        (SimplexCategory.δ (1 : Fin 2)).toOrderHom.toFun) ≫
      prod.map (((cechSimplicialObject E).map (SimplexCategory.δ (0 : Fin 2)).op).φ
        (Fin.cons i (fun _ ↦ i₀))).left (𝟙 W) =
      prod.snd ≫ prod.lift (degreeZeroDiagonal E hX q) (𝟙 W) :=
  (pairDiagonal_comp_map_of_pairLift_comp E hX q _ _ _ (pairLift_comp_faceZero E hX q i)).trans
    ((congrArg (prod.lift _) (Category.comp_id prod.snd)).symm.trans (prod.comp_lift _ _ _).symm)

end Diagonal

/-! ### Exactness of `F ⟶ Č⁰ ⟶ Č¹` -/

section Sections

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasFiniteProducts C] {X : C} (E : PreZeroHypercover.{w} X)
  [HasFiniteProducts (Over X)] [HasProducts.{w} (SheafOfModules.{w} R)]

/-- **The family of sheaves of modules whose product is the degree-`n` term of the sheaf-level
Čech complex**: at a tuple `x` of indices, the direct image `j_{U_x,*} j^{-1} F` of the fibre
product it selects.

Every projection below is spelled with this family rather than with an underscore, so that the
degree-`n` term of the complex is matched by a definitional *check* and never by whnf of a
metavariable, which does not terminate within the elaboration budget. -/
noncomputable abbrev degreeFamily (F : SheafOfModules.{w} R) (n : ℕ) :
    ((cechSimplicialObject E).obj (op (⦋n⦌ : SimplexCategory))).I → SheafOfModules.{w} R :=
  fun x ↦ ((Over.forget X).op ⋙ diagramObj R F).obj
    (op (((cechSimplicialObject E).obj (op (⦋n⦌ : SimplexCategory))).obj x))

/-- **Sections over `W` carry a product of sheaves of modules to a product of abelian groups.**
The sections functor is a composite of two forgetful functors and an evaluation, each of which
preserves products indexed by the universe of the modules. -/
noncomputable def isLimitFanSectionsOver (W : C) {ι : Type w} (M : ι → SheafOfModules.{w} R) :
    IsLimit (Fan.mk ((sectionsOver.{w} R W).obj (∏ᶜ M))
      (fun i ↦ (sectionsOver.{w} R W).map (Pi.π M i))) :=
  isLimitFanMkObjOfIsLimit (sectionsOver.{w} R W) _ _ (productIsProduct M)

omit [HasFiniteProducts C] in
/-- **The degree-zero differential of the sheaf-level Čech complex, componentwise.**  Composed
with the projection indexed by a pair `y`, it is the difference of the two transition maps of the
morphisms of fibre products that forget one of the two indices. -/
theorem d_zero_comp_pi (F : SheafOfModules.{w} R)
    (y : ((cechSimplicialObject E).obj (op (⦋1⦌ : SimplexCategory))).I) :
    ((complexFunctor R E).obj F).d 0 1 ≫ Pi.π (degreeFamily R E F 1) y =
      Pi.π (degreeFamily R E F 0)
            (((cechSimplicialObject E).map (SimplexCategory.δ (0 : Fin 2)).op).f y) ≫
          restriction R F
            (((cechSimplicialObject E).map (SimplexCategory.δ (0 : Fin 2)).op).φ y).left -
        Pi.π (degreeFamily R E F 0)
            (((cechSimplicialObject E).map (SimplexCategory.δ (1 : Fin 2)).op).f y) ≫
          restriction R F
            (((cechSimplicialObject E).map (SimplexCategory.δ (1 : Fin 2)).op).φ y).left :=
  have hd : ((complexFunctor R E).obj F).d 0 1 =
      ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (cosimplicialObj R E F).δ i :=
    Stacks.CategoryTheory.CechComplex.alternatingCofaceMapComplex_obj_d
      (cosimplicialObj R E F) 0
  (congrArg (fun z ↦ z ≫ Pi.π (degreeFamily R E F 1) y) hd).trans
    ((sum_two_zsmul_comp (fun i ↦ (cosimplicialObj R E F).δ i)
        (Pi.π (degreeFamily R E F 1) y)).trans
      ((congrArg (fun z ↦ z - (cosimplicialObj R E F).δ 1 ≫ Pi.π (degreeFamily R E F 1) y)
          (delta_comp_pi R E F 0 y)).trans
        (congrArg (fun z ↦ Pi.π (degreeFamily R E F 0) (((cechSimplicialObject E).map
              (SimplexCategory.δ (0 : Fin 2)).op).f y) ≫
            restriction R F (((cechSimplicialObject E).map
              (SimplexCategory.δ (0 : Fin 2)).op).φ y).left - z)
          (delta_comp_pi R E F 1 y))))

omit [HasFiniteProducts C] in
/-- **The sections of the augmentation are killed by the sections of the first differential.** -/
theorem sectionsOver_map_augmentation_comp_d (F : SheafOfModules.{w} R) (W : C) :
    (sectionsOver.{w} R W).map (augmentation R E F) ≫
      (sectionsOver.{w} R W).map (((complexFunctor R E).obj F).d 0 1) = 0 := by
  rw [← Functor.map_comp, augmentation_comp_d, Functor.map_zero]

omit [HasFiniteProducts C] in
/-- **The sections of the augmentation at one factor of the degree-zero term**: over `W`, the
unit `F ⟶ j_{U_x,*} j^{-1} F` is `F` applied to the projection `U_x ⨯ W ⟶ W`. -/
theorem sectionsOver_map_augmentation_comp_pi (F : SheafOfModules.{w} R) (W : C)
    (x : ((cechSimplicialObject E).obj (op (⦋0⦌ : SimplexCategory))).I) :
    (sectionsOver.{w} R W).map (augmentation R E F) ≫
        (sectionsOver.{w} R W).map (Pi.π (degreeFamily R E F 0) x) =
      F.val.presheaf.map (prod.snd :
        (((cechSimplicialObject E).obj (op (⦋0⦌ : SimplexCategory))).obj x).left ⨯ W ⟶ W).op :=
  (((sectionsOver.{w} R W).map_comp _ _).symm.trans
    (congrArg (sectionsOver.{w} R W).map (augmentation_comp_pi R E F x))).trans
      (sectionsOver_map_augmentationAt R F _ W)

omit [HasFiniteProducts C] in
/-- **The sections of the degree-zero differential at one factor of the degree-one term.** -/
theorem sectionsOver_map_d_zero_comp_pi (F : SheafOfModules.{w} R) (W : C)
    (y : ((cechSimplicialObject E).obj (op (⦋1⦌ : SimplexCategory))).I) :
    (sectionsOver.{w} R W).map (((complexFunctor R E).obj F).d 0 1) ≫
        (sectionsOver.{w} R W).map (Pi.π (degreeFamily R E F 1) y) =
      (sectionsOver.{w} R W).map (Pi.π (degreeFamily R E F 0)
            (((cechSimplicialObject E).map (SimplexCategory.δ (0 : Fin 2)).op).f y)) ≫
          (sectionsOver.{w} R W).map (restriction R F
            (((cechSimplicialObject E).map (SimplexCategory.δ (0 : Fin 2)).op).φ y).left) -
        (sectionsOver.{w} R W).map (Pi.π (degreeFamily R E F 0)
            (((cechSimplicialObject E).map (SimplexCategory.δ (1 : Fin 2)).op).f y)) ≫
          (sectionsOver.{w} R W).map (restriction R F
            (((cechSimplicialObject E).map (SimplexCategory.δ (1 : Fin 2)).op).φ y).left) :=
  (((sectionsOver.{w} R W).map_comp _ _).symm.trans
    (congrArg (sectionsOver.{w} R W).map (d_zero_comp_pi R E F y))).trans
      (map_sub_comp_comp (sectionsOver.{w} R W) _ _ _ _)

/-- Sections of a restriction map, followed by a restriction along `m`, is the restriction along
`m ≫ prod.map f (𝟙 W)`. -/
private theorem map_restriction_comp_map_op {C : Type u} [Category.{v} C] [HasBinaryProducts C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
    [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (F : SheafOfModules.{w} R) {V V' Y : C} (f : V' ⟶ V) (W : C) (m : Y ⟶ V' ⨯ W) :
    (sectionsOver.{w} R W).map (restriction R F f) ≫ F.val.presheaf.map m.op =
      F.val.presheaf.map (m ≫ prod.map f (𝟙 W)).op :=
  (congrArg (fun z ↦ z ≫ F.val.presheaf.map m.op) (sectionsOver_map_restriction R F f W)).trans
    (presheafMap_op_comp F.val.presheaf _ _)

omit [HasFiniteProducts C] [HasProducts (SheafOfModules R)] in
/-- **The homotopy undoes the second transition map, on sections.**  This is
`Stacks.CechSite.SheafLevel.pairDiagonal_comp_faceOne` read on sections over `W`. -/
theorem sectionsOver_map_restriction_faceOne_comp (hX : IsTerminal X) (F : SheafOfModules.{w} R)
    {W : C} {i₀ : E.I₀} (q : W ⟶ E.X i₀) (i : E.I₀) :
    (sectionsOver.{w} R W).map (restriction R F
          (((cechSimplicialObject E).map (SimplexCategory.δ (1 : Fin 2)).op).φ
            (Fin.cons i (fun _ ↦ i₀))).left) ≫
        F.val.presheaf.map (pairDiagonal E hX q
          ((Fin.cons i (fun _ ↦ i₀) : Fin 2 → E.I₀) ∘
            (SimplexCategory.δ (1 : Fin 2)).toOrderHom.toFun)).op = 𝟙 _ :=
  (map_restriction_comp_map_op R F _ W _).trans
    ((congrArg (fun m ↦ F.val.presheaf.map (Quiver.Hom.op m))
        (pairDiagonal_comp_faceOne E hX q i)).trans
      ((congrArg F.val.presheaf.map op_id).trans (F.val.presheaf.map_id _)))

omit [HasFiniteProducts C] [HasProducts (SheafOfModules R)] in
/-- **The homotopy turns the first transition map into the degree-zero diagonal, on sections.**
This is `Stacks.CechSite.SheafLevel.pairDiagonal_comp_faceZero` read on sections over `W`. -/
theorem map_prodLift_comp_map_snd (hX : IsTerminal X) (F : SheafOfModules.{w} R)
    {W : C} {i₀ : E.I₀} (q : W ⟶ E.X i₀) (i : E.I₀) :
    F.val.presheaf.map (prod.lift (degreeZeroDiagonal E hX q) (𝟙 W)).op ≫
        F.val.presheaf.map (prod.snd :
          (((cechSimplicialObject E).obj (op (⦋0⦌ : SimplexCategory))).obj
            ((Fin.cons i (fun _ ↦ i₀) : Fin 2 → E.I₀) ∘
              (SimplexCategory.δ (1 : Fin 2)).toOrderHom.toFun)).left ⨯ W ⟶ W).op =
      (sectionsOver.{w} R W).map (restriction R F
          (((cechSimplicialObject E).map (SimplexCategory.δ (0 : Fin 2)).op).φ
            (Fin.cons i (fun _ ↦ i₀))).left) ≫
        F.val.presheaf.map (pairDiagonal E hX q
          ((Fin.cons i (fun _ ↦ i₀) : Fin 2 → E.I₀) ∘
            (SimplexCategory.δ (1 : Fin 2)).toOrderHom.toFun)).op :=
  (presheafMap_op_comp F.val.presheaf _ _).trans
    ((congrArg (fun m ↦ F.val.presheaf.map (Quiver.Hom.op m))
        (pairDiagonal_comp_faceZero E hX q i)).symm.trans
      (map_restriction_comp_map_op R F _ W _).symm)

/-- **The retraction of the augmentation on sections over `W`**: project onto the factor of the
degree-zero term indexed by the constant tuple at `i₀` and restrict along the diagonal
`Stacks.CechSite.SheafLevel.degreeZeroDiagonal`. -/
noncomputable def sectionsRetraction (hX : IsTerminal X) (F : SheafOfModules.{w} R) {W : C}
    {i₀ : E.I₀} (q : W ⟶ E.X i₀) :
    (sectionsOver.{w} R W).obj (((complexFunctor R E).obj F).X 0) ⟶
      (sectionsOver.{w} R W).obj F :=
  (sectionsOver.{w} R W).map (Pi.π (degreeFamily R E F 0) (fun _ ↦ i₀)) ≫
    F.val.presheaf.map (prod.lift (degreeZeroDiagonal E hX q) (𝟙 W)).op

/-- **The contracting homotopy of the Čech complex of sections over `W`**: on the factor at the
degree-zero index `x` it is minus the restriction, along
`Stacks.CechSite.SheafLevel.pairDiagonal`, of the factor at the pair `(x 0, i₀)`. -/
noncomputable def sectionsHomotopy (hX : IsTerminal X) (F : SheafOfModules.{w} R) {W : C}
    {i₀ : E.I₀} (q : W ⟶ E.X i₀) :
    (sectionsOver.{w} R W).obj (((complexFunctor R E).obj F).X 1) ⟶
      (sectionsOver.{w} R W).obj (((complexFunctor R E).obj F).X 0) :=
  (isLimitFanSectionsOver R W (degreeFamily R E F 0)).lift
    (Fan.mk ((sectionsOver.{w} R W).obj (((complexFunctor R E).obj F).X 1)) (fun x ↦
      -((sectionsOver.{w} R W).map (Pi.π (degreeFamily R E F 1)
          (Fin.cons (x 0) (fun _ ↦ i₀))) ≫
        F.val.presheaf.map (pairDiagonal E hX q x).op)))

omit [HasFiniteProducts C] in
/-- The components of `Stacks.CechSite.SheafLevel.sectionsHomotopy`. -/
theorem sectionsHomotopy_comp_pi (hX : IsTerminal X) (F : SheafOfModules.{w} R) {W : C}
    {i₀ : E.I₀} (q : W ⟶ E.X i₀)
    (x : ((cechSimplicialObject E).obj (op (⦋0⦌ : SimplexCategory))).I) :
    sectionsHomotopy R E hX F q ≫ (sectionsOver.{w} R W).map (Pi.π (degreeFamily R E F 0) x) =
      -((sectionsOver.{w} R W).map (Pi.π (degreeFamily R E F 1)
          (Fin.cons (x 0) (fun _ ↦ i₀))) ≫
        F.val.presheaf.map (pairDiagonal E hX q x).op) :=
  (isLimitFanSectionsOver R W (degreeFamily R E F 0)).fac _ ⟨x⟩

omit [HasFiniteProducts C] in
/-- **Two morphisms into the degree-zero term agree as soon as their factors do.**  This is
`Stacks.CechSite.SheafLevel.isLimitFanSectionsOver` in degree zero. -/
theorem hom_ext_degreeZero (F : SheafOfModules.{w} R) (W : C) {Z : AddCommGrpCat.{w}}
    {a b : Z ⟶ (sectionsOver.{w} R W).obj (((complexFunctor R E).obj F).X 0)}
    (h : ∀ x, a ≫ (sectionsOver.{w} R W).map (Pi.π (degreeFamily R E F 0) x) =
      b ≫ (sectionsOver.{w} R W).map (Pi.π (degreeFamily R E F 0) x)) :
    a = b :=
  (isLimitFanSectionsOver R W (degreeFamily R E F 0)).hom_ext fun j ↦ by
    obtain ⟨x⟩ := j
    exact h x

omit [HasFiniteProducts C] in
/-- **The contracting identity on the factor at the index `(i, i₀) ∘ δ₁`.**  This is the algebra
of `Stacks.CechSite.SheafLevel.comp_pi_of_contracting` applied to the five identifications proved
above. -/
theorem comp_pi_sectionsRetraction_add (hX : IsTerminal X) (F : SheafOfModules.{w} R) {W : C}
    {i₀ : E.I₀} (q : W ⟶ E.X i₀) (i : E.I₀) :
    (sectionsRetraction R E hX F q ≫ (sectionsOver.{w} R W).map (augmentation R E F) +
          (sectionsOver.{w} R W).map (((complexFunctor R E).obj F).d 0 1) ≫
            sectionsHomotopy R E hX F q) ≫
        (sectionsOver.{w} R W).map (Pi.π (degreeFamily R E F 0)
          ((Fin.cons i (fun _ ↦ i₀) : Fin 2 → E.I₀) ∘
            (SimplexCategory.δ (1 : Fin 2)).toOrderHom.toFun)) =
      (sectionsOver.{w} R W).map (Pi.π (degreeFamily R E F 0)
        ((Fin.cons i (fun _ ↦ i₀) : Fin 2 → E.I₀) ∘
          (SimplexCategory.δ (1 : Fin 2)).toOrderHom.toFun)) :=
  comp_pi_of_contracting ((sectionsOver.{w} R W).map (augmentation R E F))
    ((sectionsOver.{w} R W).map (((complexFunctor R E).obj F).d 0 1))
    (sectionsRetraction R E hX F q) (sectionsHomotopy R E hX F q)
    ((sectionsOver.{w} R W).map (Pi.π (degreeFamily R E F 0)
      ((Fin.cons i (fun _ ↦ i₀) : Fin 2 → E.I₀) ∘
        (SimplexCategory.δ (1 : Fin 2)).toOrderHom.toFun)))
    ((sectionsOver.{w} R W).map (Pi.π (degreeFamily R E F 1) (Fin.cons i (fun _ ↦ i₀))))
    ((sectionsOver.{w} R W).map (Pi.π (degreeFamily R E F 0) (fun _ ↦ i₀))) _ _ _ _
    (sectionsOver_map_augmentation_comp_pi R E F W _)
    (sectionsHomotopy_comp_pi R E hX F q _)
    (sectionsOver_map_d_zero_comp_pi R E F W (Fin.cons i (fun _ ↦ i₀)))
    ((Category.assoc _ _ _).trans
      (congrArg (fun z ↦ (sectionsOver.{w} R W).map
          (Pi.π (degreeFamily R E F 0) (fun _ ↦ i₀)) ≫ z)
        (map_prodLift_comp_map_snd R E hX F q i)))
    (sectionsOver_map_restriction_faceOne_comp R E hX F q i)

omit [HasFiniteProducts C] in
/-- **The contracting identity for the Čech complex of sections over `W`.**  The retraction
`Stacks.CechSite.SheafLevel.sectionsRetraction` and the homotopy
`Stacks.CechSite.SheafLevel.sectionsHomotopy` satisfy `r ≫ aug + d⁰ ≫ s = 𝟙` on `Γ(W, Č⁰)`.

It is checked on each factor of the degree-zero product, the factor being first put in the form
`(x 0, i₀) ∘ δ₁` by `Stacks.CechSite.SheafLevel.degreeZeroIndex_eq`. -/
theorem sectionsRetraction_comp_add (hX : IsTerminal X) (F : SheafOfModules.{w} R) {W : C}
    {i₀ : E.I₀} (q : W ⟶ E.X i₀) :
    sectionsRetraction R E hX F q ≫ (sectionsOver.{w} R W).map (augmentation R E F) +
        (sectionsOver.{w} R W).map (((complexFunctor R E).obj F).d 0 1) ≫
          sectionsHomotopy R E hX F q =
      𝟙 ((sectionsOver.{w} R W).obj (((complexFunctor R E).obj F).X 0)) := by
  refine hom_ext_degreeZero R E F W fun x ↦ ?_
  obtain ⟨i, rfl⟩ := degreeZeroIndex_eq E i₀ x
  exact (comp_pi_sectionsRetraction_add R E hX F q i).trans (Category.id_comp _).symm

omit [HasFiniteProducts C] in
/-- **Over an object mapping to a member of the family, the complex of sections
`F(W) ⟶ Γ(W, Č⁰) ⟶ Γ(W, Č¹)` is exact.**

The family is not assumed covering and the coefficients are not assumed to satisfy any sheaf
condition: a morphism `q : W ⟶ U_{i₀}` makes the Čech complex of sections over `W` contractible in
degree zero, by `Stacks.CechSite.SheafLevel.sectionsRetraction_comp_add`.  Terminality of `X` is
what makes the two morphisms the retraction and the homotopy are built from exist. -/
theorem exact_sectionsOver_shortComplex (hX : IsTerminal X) (F : SheafOfModules.{w} R) {W : C}
    {i₀ : E.I₀} (q : W ⟶ E.X i₀) :
    (ShortComplex.mk ((sectionsOver.{w} R W).map (augmentation R E F))
      ((sectionsOver.{w} R W).map (((complexFunctor R E).obj F).d 0 1))
      (sectionsOver_map_augmentation_comp_d R E F W)).Exact :=
  CategoryTheory.SimplicialSiteSituation.exact_of_contracting _
    (sectionsRetraction R E hX F q) (sectionsHomotopy R E hX F q)
    (sectionsRetraction_comp_add R E hX F q)

variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [HasFiniteProducts C] in
/-- **The short complex `F ⟶ Č⁰ ⟶ Č¹` of the sheaf-level Čech complex of a family covering a
terminal object is exact.**

Together with `Stacks.CechSite.SheafLevel.mono_augmentation_of_coversTop` this says that the
augmentation is a kernel of `d⁰`; see
`Stacks.CechSite.SheafLevel.isLimit_augmentationFork_of_coversTop`.  Exactness is read off the
locality criterion `Stacks.SheafOfModules.ComplexLocality.exact_of_coversTop`: over an object `W`
mapping to a member of the family the complex of sections is exact by
`Stacks.CechSite.SheafLevel.exact_sectionsOver_shortComplex`, and
`CategoryTheory.ShortComplex.ab_exact_iff` turns that into the sectionwise statement the criterion
consumes. -/
theorem exact_shortComplex_augmentation_of_coversTop (hX : IsTerminal X) (hE : J.CoversTop E.X)
    (F : SheafOfModules.{w} R) :
    (ShortComplex.mk (augmentation R E F) (((complexFunctor R E).obj F).d 0 1)
      (augmentation_comp_d R E F)).Exact := by
  refine Stacks.SheafOfModules.ComplexLocality.exact_of_coversTop hE _ (fun i₀ W q z hz ↦ ?_)
  have hex := exact_sectionsOver_shortComplex R E hX F q
  rw [ShortComplex.ab_exact_iff] at hex
  exact hex z hz

/-- **The augmentation of the sheaf-level Čech complex of a family covering a terminal object is
a kernel of the first differential.**  This is the degree-zero statement in the form
`CategoryTheory.ShortComplex.exact_and_mono_f_iff_f_is_kernel` packages it: exactness of
`F ⟶ Č⁰ ⟶ Č¹` together with `Stacks.CechSite.SheafLevel.mono_augmentation_of_coversTop`. -/
noncomputable def isLimit_augmentationFork_of_coversTop (hX : IsTerminal X)
    (hE : J.CoversTop E.X) (F : SheafOfModules.{w} R) :
    IsLimit (KernelFork.ofι (augmentation R E F) (augmentation_comp_d R E F)) :=
  Nonempty.some ((ShortComplex.exact_and_mono_f_iff_f_is_kernel _).1
    ⟨exact_shortComplex_augmentation_of_coversTop R E hX hE F,
      mono_augmentation_of_coversTop R E hX hE F⟩)

variable [HasZeroObject (SheafOfModules.{w} R)]

/-- **The augmentation is a quasi-isomorphism in degree zero.**  By
`CochainComplex.quasiIsoAt₀_iff` and `CategoryTheory.ShortComplex.quasiIso_iff_of_zeros` this is
exactness of `F ⟶ Č⁰ ⟶ Č¹` together with the augmentation being a monomorphism. -/
theorem quasiIsoAt_augmentationHom_zero_of_coversTop (hX : IsTerminal X) (hE : J.CoversTop E.X)
    (F : SheafOfModules.{w} R) : QuasiIsoAt (augmentationHom R E F) 0 := by
  have hf0 : ∀ K : CochainComplex (SheafOfModules.{w} R) ℕ, K.d 0 0 = 0 :=
    fun K ↦ K.shape 0 0 (by simp)
  refine (CochainComplex.quasiIsoAt₀_iff _).2
    ((ShortComplex.quasiIso_iff_of_zeros _ (hf0 ((CochainComplex.single₀ _).obj F)) ?_
      (hf0 ((complexFunctor R E).obj F))).2 ⟨?_, ?_⟩)
  · rfl
  · exact exact_shortComplex_augmentation_of_coversTop R E hX hE F
  · exact mono_augmentation_of_coversTop R E hX hE F

variable [∀ W : C, HasFiniteProducts (Over W)]

omit [HasFiniteProducts (Over X)] in
/-- **The augmentation is a quasi-isomorphism in every degree.**  Above degree zero this is
`Stacks.CechSite.SheafLevel.exactAt_complexFunctor_of_coversTop`, which is where the hypothesis
that every slice of the site has finite products enters; the degree-zero statements above do not
use it. -/
theorem quasiIsoAt_augmentationHom_of_coversTop (hX : IsTerminal X) (hE : J.CoversTop E.X)
    (F : SheafOfModules.{w} R) (n : ℕ) : QuasiIsoAt (augmentationHom R E F) n := by
  obtain _ | m := n
  · exact quasiIsoAt_augmentationHom_zero_of_coversTop R E hX hE F
  · rw [quasiIsoAt_iff_exactAt _ _
      (HomologicalComplex.exactAt_single_obj (ComplexShape.up ℕ) 0 F (m + 1) (by omega))]
    exact exactAt_complexFunctor_of_coversTop R E hX hE F (m + 1) (by omega)

omit [HasFiniteProducts (Over X)] in
/-- **The Čech complex of a family covering a terminal object is a resolution of `F`**: the
augmentation `F[0] ⟶ Č(E, F)` of `Stacks.CechSite.SheafLevel.augmentationHom` is a
quasi-isomorphism.

This is the statement [Stacks, Tag 03AT] gives for the Čech complex of a covering, with sheaves of
modules as coefficients, and it is the shape in which a resolution is consumed: in positive
degrees it is exactness of the complex
(`Stacks.CechSite.SheafLevel.exactAt_complexFunctor_of_coversTop`), and in degree zero it is
exactness of `F ⟶ Č⁰ ⟶ Č¹`
(`Stacks.CechSite.SheafLevel.exact_shortComplex_augmentation_of_coversTop`) together with the
augmentation being a monomorphism
(`Stacks.CechSite.SheafLevel.mono_augmentation_of_coversTop`).

Terminality of `X` cannot be dropped: for a non-terminal target the complex is not a resolution,
by the counterexample recorded in the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Cech/SheafLevelComplexSections.lean`. -/
theorem quasiIso_augmentationHom_of_coversTop (hX : IsTerminal X) (hE : J.CoversTop E.X)
    (F : SheafOfModules.{w} R) : QuasiIso (augmentationHom R E F) :=
  ⟨quasiIsoAt_augmentationHom_of_coversTop R E hX hE F⟩

end Sections

end Stacks.CechSite.SheafLevel

end
