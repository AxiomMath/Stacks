module

public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksFrontier.AlgebraicGeometry.Descent.Module.Amitsur

/-!
# The Čech conerve of an algebra map, shifted by one degree

For a commutative `R`-algebra `A`, the Čech conerve of the structure arrow `R ⟶ A` in
commutative `R`-algebras is the cosimplicial `R`-algebra `(A/R)•` whose value in degree `n`
is the `(n + 1)`-fold tensor power of `A` over `R`. This file identifies its value in degree
`n + 1` with `A ⊗[R] (A/R)ₙ`, naturally in `n`.

The identification is the algebraic shadow of the décalage of a cosimplicial object: the
degree-`n` part of the shifted object is the degree-`(n + 1)` part of the original, and the
shifted coface maps are the original ones tensored with the identity of `A`. It is stated
through the universal properties alone — the Čech conerve is an abstract wide pushout, never a
concrete tensor power — so the forward map is a `WidePushout.desc` and the backward map an
`Algebra.TensorProduct.lift`.

## Main definitions

* `Stacks.Descent.algebraArrow` is the arrow `R ⟶ A` in `CommAlgCat R`.
* `Stacks.Descent.cechTensorObj` is `A ⊗[R] (A/R)ₙ` as a commutative `R`-algebra.
* `Stacks.Descent.cechTensorMap` is the functorial action of `A ⊗[R] -` on `(A/R)•`.
* `Stacks.Descent.cechShiftIso` is the identification `(A/R)_{n + 1} ≅ A ⊗[R] (A/R)ₙ`.

## Main results

* `Stacks.Descent.cechShiftFwd_naturality` says that `cechShiftIso` carries a cosimplicial
  structure map of `(A/R)•` that fixes the leading index to the corresponding structure map
  tensored with the identity. Applied to the coface maps it identifies the shifted alternating
  coface complex with the base change of the unshifted one along `R ⟶ A`.
* `Stacks.Descent.cechShiftBwd_comp_sigma` identifies the first codegeneracy of `(A/R)•` with
  multiplication of the leading tensor factor into `(A/R)ₙ`. This is the contraction underlying
  the acyclicity of the shifted complex.
* `Stacks.Descent.algebraMapArrow_eq` identifies `algebraArrow` with the arrow used to build the
  extended Amitsur cochain complex, so the results here apply to that complex.

## References

* [Stacks Project, Tag 023K](https://stacks.math.columbia.edu/tag/023K)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Arrow
open scoped TensorProduct

universe u v

namespace Stacks.Descent

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]

/-- The structure arrow `R ⟶ A` in the category of commutative `R`-algebras. Its Čech conerve
is the cosimplicial `R`-algebra `(A/R)•`. -/
noncomputable abbrev algebraArrow : Arrow (CommAlgCat.{u} R) :=
  Arrow.mk (CommAlgCat.ofHom (Algebra.ofId R A))

/-- Two morphisms out of the source of `algebraArrow` agree: it is the base algebra. -/
lemma algebraArrow_left_hom_ext {Z : CommAlgCat.{u} R} (g₁ g₂ : (algebraArrow R A).left ⟶ Z) :
    g₁ = g₂ :=
  CommAlgCat.hom_ext (Subsingleton.elim (α := (R →ₐ[R] Z)) _ _)

/-- `A ⊗[R] (A/R)ₙ`, as a commutative `R`-algebra. -/
noncomputable def cechTensorObj (n : SimplexCategory) : CommAlgCat.{u} R :=
  CommAlgCat.of R (A ⊗[R] ((algebraArrow R A).cechConerve.obj n : Type u))

/-- The functor `A ⊗[R] -` applied to a cosimplicial structure map of `(A/R)•`. -/
noncomputable def cechTensorMap {n m : SimplexCategory} (g : n ⟶ m) :
    cechTensorObj R A n ⟶ cechTensorObj R A m :=
  ConcreteCategory.ofHom
    (Algebra.TensorProduct.map (AlgHom.id R A) ((algebraArrow R A).cechConerve.map g).hom)

/-- The identification `(A/R)_{n + 1} ⟶ A ⊗[R] (A/R)ₙ`: the leading tensor factor is the
zeroth Čech coprojection, and the remaining factors are the Čech coprojections of `(A/R)ₙ`. -/
noncomputable def cechShiftFwd (n : ℕ) :
    (algebraArrow R A).cechConerve.obj (.mk (n + 1)) ⟶ cechTensorObj R A (.mk n) :=
  WidePushout.desc (arrows := cechLegs (algebraArrow R A) (.mk (n + 1)))
    (ConcreteCategory.ofHom (Algebra.ofId R _))
    (fun i => i.cases (ConcreteCategory.ofHom Algebra.TensorProduct.includeLeft)
      (fun j => cechι (f := algebraArrow R A) (.mk n) j ≫
        ConcreteCategory.ofHom Algebra.TensorProduct.includeRight))
    (fun _ => algebraArrow_left_hom_ext R A _ _)

/-- The identification `A ⊗[R] (A/R)ₙ ⟶ (A/R)_{n + 1}`, inverse to `cechShiftFwd`. -/
noncomputable def cechShiftBwd (n : ℕ) :
    cechTensorObj R A (.mk n) ⟶ (algebraArrow R A).cechConerve.obj (.mk (n + 1)) :=
  ConcreteCategory.ofHom (Algebra.TensorProduct.lift
    (cechι (f := algebraArrow R A) (.mk (n + 1)) 0).hom
    ((algebraArrow R A).cechConerve.map (SimplexCategory.δ (0 : Fin (n + 2)))).hom
    (fun _ _ => Commute.all _ _))

/-- The zeroth coface map of `SimplexCategory` is `Fin.succ`. -/
lemma delta_zero_toOrderHom (n : ℕ) (j : Fin (n + 1)) :
    (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom j = j.succ := by
  simp [SimplexCategory.δ]

/-- `cechShiftFwd` sends the zeroth Čech coprojection to the leading tensor factor. -/
@[simp]
lemma cechι_zero_comp_cechShiftFwd (n : ℕ) :
    cechι (f := algebraArrow R A) (.mk (n + 1)) 0 ≫ cechShiftFwd R A n =
      ConcreteCategory.ofHom Algebra.TensorProduct.includeLeft :=
  WidePushout.ι_desc _ _ _ _ 0

/-- `cechShiftFwd` sends the `(j + 1)`-st Čech coprojection to the `j`-th one of `(A/R)ₙ`. -/
@[simp]
lemma cechι_succ_comp_cechShiftFwd (n : ℕ) (j : Fin (n + 1)) :
    cechι (f := algebraArrow R A) (.mk (n + 1)) j.succ ≫ cechShiftFwd R A n =
      cechι (f := algebraArrow R A) (.mk n) j ≫
        ConcreteCategory.ofHom Algebra.TensorProduct.includeRight :=
  WidePushout.ι_desc _ _ _ _ j.succ

/-- `cechShiftBwd` sends the leading tensor factor to the zeroth Čech coprojection. -/
@[simp]
lemma includeLeft_comp_cechShiftBwd (n : ℕ) :
    (ConcreteCategory.ofHom Algebra.TensorProduct.includeLeft :
        CommAlgCat.of R A ⟶ cechTensorObj R A (.mk n)) ≫ cechShiftBwd R A n =
      cechι (f := algebraArrow R A) (.mk (n + 1)) 0 :=
  CommAlgCat.hom_ext
    (Algebra.TensorProduct.lift_comp_includeLeft _ _ (fun _ _ => Commute.all _ _))

/-- `cechShiftBwd` restricted to `(A/R)ₙ` is the zeroth coface map. -/
@[simp]
lemma includeRight_comp_cechShiftBwd (n : ℕ) :
    (ConcreteCategory.ofHom Algebra.TensorProduct.includeRight :
        (algebraArrow R A).cechConerve.obj (.mk n) ⟶ cechTensorObj R A (.mk n)) ≫
      cechShiftBwd R A n =
      (algebraArrow R A).cechConerve.map (SimplexCategory.δ (0 : Fin (n + 2))) :=
  CommAlgCat.hom_ext
    (Algebra.TensorProduct.lift_comp_includeRight _ _ (fun _ _ => Commute.all _ _))

/-- `cechShiftFwd` is a split monomorphism with retraction `cechShiftBwd`. -/
lemma cechShiftFwd_cechShiftBwd (n : ℕ) :
    cechShiftFwd R A n ≫ cechShiftBwd R A n = 𝟙 _ := by
  apply cech_hom_ext (f := algebraArrow R A)
  intro i
  rw [← Category.assoc]
  induction i using Fin.cases with
  | zero =>
    rw [cechι_zero_comp_cechShiftFwd, Category.comp_id, includeLeft_comp_cechShiftBwd]
  | succ j =>
    rw [cechι_succ_comp_cechShiftFwd, Category.assoc, includeRight_comp_cechShiftBwd,
      cechι_comp_map, Category.comp_id, delta_zero_toOrderHom]

/-- The zeroth coface map of `(A/R)•` is the inclusion of the non-leading tensor factors. -/
lemma map_delta_zero_comp_cechShiftFwd (n : ℕ) :
    (algebraArrow R A).cechConerve.map (SimplexCategory.δ (0 : Fin (n + 2))) ≫
        cechShiftFwd R A n =
      ConcreteCategory.ofHom Algebra.TensorProduct.includeRight := by
  apply cech_hom_ext (f := algebraArrow R A)
  intro j
  rw [← Category.assoc, cechι_comp_map, delta_zero_toOrderHom, cechι_succ_comp_cechShiftFwd]

/-- Two morphisms out of `A ⊗[R] (A/R)ₙ` agree if they agree on both tensor factors. -/
private theorem cechTensorObj_hom_ext {n : SimplexCategory} {X : CommAlgCat.{u} R}
    {f g : cechTensorObj R A n ⟶ X}
    (hl : (ConcreteCategory.ofHom Algebra.TensorProduct.includeLeft :
        CommAlgCat.of R A ⟶ cechTensorObj R A n) ≫ f = ConcreteCategory.ofHom
          Algebra.TensorProduct.includeLeft ≫ g)
    (hr : (ConcreteCategory.ofHom Algebra.TensorProduct.includeRight :
        (algebraArrow R A).cechConerve.obj n ⟶ cechTensorObj R A n) ≫ f =
      ConcreteCategory.ofHom Algebra.TensorProduct.includeRight ≫ g) :
    f = g :=
  CommAlgCat.hom_ext (Algebra.TensorProduct.ext (congrArg CommAlgCat.Hom.hom hl)
    (AlgHom.ext fun x => congr($hr x)))

/-- `cechShiftBwd` is a split monomorphism with retraction `cechShiftFwd`. -/
lemma cechShiftBwd_cechShiftFwd (n : ℕ) :
    cechShiftBwd R A n ≫ cechShiftFwd R A n = 𝟙 _ := by
  apply cechTensorObj_hom_ext
  · rw [← Category.assoc, includeLeft_comp_cechShiftBwd, cechι_zero_comp_cechShiftFwd,
      Category.comp_id]
  · rw [← Category.assoc, includeRight_comp_cechShiftBwd, map_delta_zero_comp_cechShiftFwd,
      Category.comp_id]

/-- The degree-`(n + 1)` part of the Čech conerve of `R ⟶ A` is `A ⊗[R]` its degree-`n` part. -/
noncomputable def cechShiftIso (n : ℕ) :
    (algebraArrow R A).cechConerve.obj (.mk (n + 1)) ≅ cechTensorObj R A (.mk n) where
  hom := cechShiftFwd R A n
  inv := cechShiftBwd R A n
  hom_inv_id := cechShiftFwd_cechShiftBwd R A n
  inv_hom_id := cechShiftBwd_cechShiftFwd R A n

/-- `cechTensorMap` acts as the given structure map on the non-leading tensor factor. -/
@[simp]
lemma includeRight_comp_cechTensorMap {n m : SimplexCategory} (g : n ⟶ m) :
    (ConcreteCategory.ofHom Algebra.TensorProduct.includeRight :
        (algebraArrow R A).cechConerve.obj n ⟶ cechTensorObj R A n) ≫ cechTensorMap R A g =
      (algebraArrow R A).cechConerve.map g ≫
        ConcreteCategory.ofHom Algebra.TensorProduct.includeRight :=
  CommAlgCat.hom_ext (Algebra.TensorProduct.map_comp_includeRight (AlgHom.id R A) _)

/-- `cechTensorMap` is the identity on the leading tensor factor. -/
@[simp]
lemma includeLeft_comp_cechTensorMap {n m : SimplexCategory} (g : n ⟶ m) :
    (ConcreteCategory.ofHom Algebra.TensorProduct.includeLeft :
        CommAlgCat.of R A ⟶ cechTensorObj R A n) ≫ cechTensorMap R A g =
      ConcreteCategory.ofHom Algebra.TensorProduct.includeLeft :=
  CommAlgCat.hom_ext
    ((Algebra.TensorProduct.map_comp_includeLeft (AlgHom.id R A) _).trans (AlgHom.comp_id _))

/-- A cosimplicial structure map of `(A/R)•` that fixes the leading index and acts as `g` on the
remaining ones is carried by `cechShiftIso` to `A ⊗[R] g`. Taking `h` to be `δ (i + 1)` and `g`
to be `δ i` identifies the shifted alternating coface complex with the base change of the
unshifted one along `R ⟶ A`. -/
lemma cechShiftFwd_naturality {n m : ℕ} (g : SimplexCategory.mk n ⟶ .mk m)
    (h : SimplexCategory.mk (n + 1) ⟶ .mk (m + 1)) (h₀ : h.toOrderHom 0 = 0)
    (hs : ∀ j : Fin (n + 1), h.toOrderHom j.succ = (g.toOrderHom j).succ) :
    (algebraArrow R A).cechConerve.map h ≫ cechShiftFwd R A m =
      cechShiftFwd R A n ≫ cechTensorMap R A g := by
  apply cech_hom_ext (f := algebraArrow R A)
  intro i
  rw [← Category.assoc, ← Category.assoc, cechι_comp_map]
  induction i using Fin.cases with
  | zero =>
    rw [h₀, cechι_zero_comp_cechShiftFwd, cechι_zero_comp_cechShiftFwd,
      includeLeft_comp_cechTensorMap]
  | succ j =>
    rw [hs j, cechι_succ_comp_cechShiftFwd, cechι_succ_comp_cechShiftFwd, Category.assoc,
      includeRight_comp_cechTensorMap, ← Category.assoc, cechι_comp_map]

/-- Multiplication of the leading tensor factor of `A ⊗[R] (A/R)ₙ` into `(A/R)ₙ`, along the
zeroth Čech coprojection. -/
noncomputable def cechTensorMul (n : ℕ) :
    cechTensorObj R A (.mk n) ⟶ (algebraArrow R A).cechConerve.obj (.mk n) :=
  ConcreteCategory.ofHom (Algebra.TensorProduct.lift
    (cechι (f := algebraArrow R A) (.mk n) 0).hom (AlgHom.id R _)
    (fun _ _ => Commute.all _ _))

/-- The zeroth codegeneracy of `SimplexCategory` fixes `0`. -/
lemma sigma_zero_toOrderHom_zero (n : ℕ) :
    (SimplexCategory.σ (0 : Fin (n + 1))).toOrderHom 0 = 0 := by
  simp [SimplexCategory.σ]

/-- The first codegeneracy of `(A/R)•` multiplies the leading tensor factor into `(A/R)ₙ`: this
is the contraction that makes the shifted complex acyclic. -/
lemma cechShiftBwd_comp_sigma (n : ℕ) :
    cechShiftBwd R A n ≫
        (algebraArrow R A).cechConerve.map (SimplexCategory.σ (0 : Fin (n + 1))) =
      cechTensorMul R A n := by
  apply cechTensorObj_hom_ext
  · rw [← Category.assoc, includeLeft_comp_cechShiftBwd, cechι_comp_map,
      sigma_zero_toOrderHom_zero]
    exact (CommAlgCat.hom_ext
      (Algebra.TensorProduct.lift_comp_includeLeft _ _ (fun _ _ => Commute.all _ _))).symm
  · rw [← Category.assoc, includeRight_comp_cechShiftBwd, ← Functor.map_comp,
      show SimplexCategory.δ (0 : Fin (n + 2)) = SimplexCategory.δ (0 : Fin (n + 1)).castSucc by
        rw [Fin.castSucc_zero],
      SimplexCategory.δ_comp_σ_self, CategoryTheory.Functor.map_id]
    exact (CommAlgCat.hom_ext
      (Algebra.TensorProduct.lift_comp_includeRight' _ _ (fun _ _ => Commute.all _ _))).symm

/-- The arrow whose Čech conerve builds the extended Amitsur cochain complex is `algebraArrow`
for the universe-lifted rings. -/
lemma algebraMapArrow_eq (R₀ : Type u) (A₀ : Type v) [CommRing R₀] [CommRing A₀]
    [Algebra R₀ A₀] :
    AlgebraicTopology.algebraMapArrow R₀ A₀ =
      @algebraArrow (ULift.{v} R₀) _ (ULift.{u} A₀) _ (ULift.algebra' R₀ (ULift.{u} A₀)) :=
  rfl

end Stacks.Descent

end
