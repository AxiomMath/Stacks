module

public import StacksFrontier.CategoryTheory.Sites.CechComplex

/-!
# Reindexing the Čech complex along an equivalence of index types

Mathlib's `CategoryTheory.cechComplexFunctor` is attached to a *family* `U : ι → C`, not to the
set of its members, and its degree `n` term is a product indexed by the tuples
`Fin (n + 1) → ι`. Two families that differ by a bijection of index types therefore have Čech
complexes that are isomorphic but not equal.

Given `U : ι → C` and an equivalence `e : ι' ≃ ι`, the Čech complex of the reindexed family
`fun i ↦ U (e i)` is isomorphic to the Čech complex of `U`, compatibly with the differentials,
and hence has the same cohomology.

The index types `ι` and `ι'` are allowed to live in **different universes**: a covering produced
as a finite family is indexed by `Fin n : Type 0`, while a covering packaged as a structure whose
index type is required to live in the universe of the ambient space is indexed by some `Type u`.
Statements about the two are not interchangeable, and `ULift` does not help — the two Čech
complexes are genuinely different objects, built from products over different index types, and
must be compared by a map.

## Main definitions

* `Stacks.CategoryTheory.CechReindex.fwd`: the comparison map, in each degree, from the Čech
  complex of `U` to the Čech complex of the reindexed family. Its component at the tuple
  `x : Fin (n + 1) → ι'` is the projection of the Čech complex of `U` onto the factor indexed by
  the reindexed tuple `fun a ↦ e (x a)`.
* `Stacks.CategoryTheory.CechReindex.bwd`: the inverse comparison map, built from `e.symm`.
* `Stacks.CategoryTheory.CechReindex.cechIso`: the resulting isomorphism of cochain complexes.

## Main results

* `Stacks.CategoryTheory.CechReindex.isZero_homology_of_reindex`: vanishing of the Čech
  cohomology of `U` in a degree transfers to the reindexed family.
* `Stacks.CategoryTheory.CechReindex.fwd_comm`: the comparison map commutes with the Čech
  differentials.
* `Stacks.CategoryTheory.CechReindex.inter_reindex`: reindexing a family and reindexing a tuple
  select the same intersection.

## Implementation notes

**Why `fun i ↦ U (e i)` and not `U ∘ e`.** The two are definitionally equal, but the comparison
map is built by feeding a projection of one Čech complex into the universal property of the
other, and that only elaborates when the two intersection objects are syntactically close
enough: `inter (fun i ↦ U (e i)) x` and `inter U (fun a ↦ e (x a))` both beta-reduce to the
product of the `U (e (x a))`, whereas spelling either side with `Function.comp` interposes a
definition the unifier then has to be asked to unfold. For the same reason the tuples are
written `fun a ↦ e (x a)` rather than `e ∘ x` throughout.

**Why the proofs are in term mode.** The two Čech complexes have degree `n` terms whose factors
are *definitionally* but not syntactically equal, so a `rewrite` that replaces a projection of
one complex by a projection of the other leaves a goal that is type-correct only after `inter`
is unfolded. Any later `rewrite` in the same goal then fails to find its pattern. Every
composite below is therefore assembled with `Eq.trans` and `congrArg`, which do their unification
at default transparency, and `rewrite` is used only inside a single step that does not change the
target object of the morphism.

**The one `eqToHom`.** The forward map needs no transport: its components are literally
projections of the Čech complex of `U`. The backward map does, because its component at a tuple
`y : Fin (n + 1) → ι` is a projection at the tuple `fun a ↦ e (e.symm (y a))`, which equals `y`
only propositionally. That single transport is isolated in `bwd` and discharged by `pi_congr`,
which is proved by substituting the equality of tuples; no `eqToHom` appears in the statement of
any result below except `bwd_comp_π`, which unfolds the definition of `bwd`.

**Degreewise, then assembled.** `fwd` is defined one degree at a time and shown to be a
degreewise isomorphism commuting with the differentials, and only then assembled by
`HomologicalComplex.Hom.isoOfComponents`. Going through `CategoryTheory.Limits.FormalCoproduct`
instead — an isomorphism of formal coproducts induces one of Čech complexes, by functoriality of
`FormalCoproduct.cechFunctor` — is shorter but **cannot** be used here: `FormalCoproduct.{w} C`
fixes the universe of the index type in the category itself, so two families indexed in different
universes give objects of two different categories and there is no isomorphism to speak of.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' v v' u u'

namespace Stacks.CategoryTheory.CechReindex

open Stacks.CategoryTheory.CechComplex

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [HasFiniteProducts C] [Preadditive A] {ι : Type w} {ι' : Type w'}

/-! ### Reindexing an intersection -/

/-- **Reindexing commutes with intersections.** The intersection selected by a tuple `x` in the
reindexed family is the intersection selected by the reindexed tuple in the original family.
Both sides are the product of the objects `U (e (x a))`, so this holds by definition. -/
theorem inter_reindex (U : ι → C) (e : ι' → ι) {m : ℕ} (x : Fin m → ι') :
    inter (fun i ↦ U (e i)) x = inter U (fun a ↦ e (x a)) :=
  rfl

/-! ### Transporting a projection along an equality of tuples -/

variable [HasProducts.{w} A] (U : ι → C) (P : Cᵒᵖ ⥤ A)

/-- **Projections at equal tuples agree.** Two equal tuples select the same factor of the degree
`n` term of the Čech complex, and the projections onto those factors agree after the transport
induced by the equality. -/
theorem pi_congr {n : ℕ} {x y : Fin (n + 1) → ι} (h : x = y) :
    π U P n x ≫ eqToHom (congrArg (fun z ↦ P.obj (op (inter U z))) h) = π U P n y := by
  subst h
  simp

/-! ### The comparison maps -/

variable [HasProducts.{w'} A] (e : ι' ≃ ι)

/-- **The comparison map from the Čech complex of `U` to that of the reindexed family**, in
degree `n`. Its component at the tuple `x : Fin (n + 1) → ι'` is the projection of the degree
`n` term of the Čech complex of `U` onto the factor indexed by the reindexed tuple
`fun a ↦ e (x a)`; no transport is needed because the two intersection objects agree by
`inter_reindex`. -/
noncomputable def fwd (n : ℕ) :
    ((cechComplexFunctor U).obj P).X n ⟶
      ((cechComplexFunctor (fun i ↦ U (e i))).obj P).X n :=
  lift (fun i ↦ U (e i)) P fun x ↦ π U P n fun a ↦ e (x a)

/-- The component of `fwd` at the tuple `x` is the projection of the Čech complex of `U` at the
reindexed tuple `fun a ↦ e (x a)`. -/
@[reassoc]
theorem fwd_comp_π (n : ℕ) (x : Fin (n + 1) → ι') :
    fwd U P e n ≫ π (fun i ↦ U (e i)) P n x = π U P n (fun a ↦ e (x a)) :=
  lift_comp_π _ P _ x

/-- **The comparison map from the Čech complex of the reindexed family to that of `U`**, in
degree `n`. Its component at the tuple `y : Fin (n + 1) → ι` is the projection of the reindexed
Čech complex at `fun a ↦ e.symm (y a)`, transported along the equality
`(fun a ↦ e (e.symm (y a))) = y`. -/
noncomputable def bwd (n : ℕ) :
    ((cechComplexFunctor (fun i ↦ U (e i))).obj P).X n ⟶
      ((cechComplexFunctor U).obj P).X n :=
  lift U P fun y ↦
    π (fun i ↦ U (e i)) P n (fun a ↦ e.symm (y a)) ≫
      eqToHom (congrArg (fun z ↦ P.obj (op (inter U z)))
        (funext fun a ↦ e.apply_symm_apply (y a)))

/-- The component of `bwd` at the tuple `y` is the projection of the reindexed Čech complex at
`fun a ↦ e.symm (y a)`, followed by the transport along `(fun a ↦ e (e.symm (y a))) = y`. -/
@[reassoc]
theorem bwd_comp_π (n : ℕ) (y : Fin (n + 1) → ι) :
    bwd U P e n ≫ π U P n y =
      π (fun i ↦ U (e i)) P n (fun a ↦ e.symm (y a)) ≫
        eqToHom (congrArg (fun z ↦ P.obj (op (inter U z)))
          (funext fun a ↦ e.apply_symm_apply (y a))) :=
  lift_comp_π U P _ y

/-- The two comparison maps compose to the identity on the Čech complex of `U`. -/
theorem fwd_comp_bwd (n : ℕ) : fwd U P e n ≫ bwd U P e n = 𝟙 _ :=
  hom_ext U P fun y ↦ by
    rw [Category.id_comp, Category.assoc, bwd_comp_π, fwd_comp_π_assoc]
    exact pi_congr U P (funext fun a ↦ e.apply_symm_apply (y a))

/-- The two comparison maps compose to the identity on the Čech complex of the reindexed
family. -/
theorem bwd_comp_fwd (n : ℕ) : bwd U P e n ≫ fwd U P e n = 𝟙 _ :=
  hom_ext (fun i ↦ U (e i)) P fun x ↦ by
    rw [Category.id_comp, Category.assoc]
    exact ((congrArg (bwd U P e n ≫ ·) (fwd_comp_π U P e n x)).trans
      (bwd_comp_π U P e n (fun a ↦ e (x a)))).trans
        (pi_congr (fun i ↦ U (e i)) P (funext fun a ↦ e.symm_apply_apply (x a)))

/-- **The comparison map followed by the Čech differential of the reindexed family**,
componentwise: the alternating sum of the restrictions along the face maps, read in the Čech
complex of `U`. -/
theorem fwd_comp_d_comp_π (n : ℕ) (x : Fin (n + 2) → ι') :
    fwd U P e n ≫ ((cechComplexFunctor (fun i ↦ U (e i))).obj P).d n (n + 1) ≫
        π (fun i ↦ U (e i)) P (n + 1) x =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        (π U P n ((fun a ↦ e (x a)) ∘ i.succAbove) ≫
          P.map (interMap U (fun a ↦ e (x a)) i.succAbove).op) := by
  rw [d_comp_π, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Preadditive.comp_zsmul, fwd_comp_π_assoc]
  exact rfl

/-- **The Čech differential of `U` followed by the comparison map**, componentwise: the same
alternating sum. The two Čech complexes have the same face maps because reindexing a tuple
commutes with omitting one of its entries. -/
theorem d_comp_fwd_comp_π (n : ℕ) (x : Fin (n + 2) → ι') :
    ((cechComplexFunctor U).obj P).d n (n + 1) ≫ fwd U P e (n + 1) ≫
        π (fun i ↦ U (e i)) P (n + 1) x =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        (π U P n ((fun a ↦ e (x a)) ∘ i.succAbove) ≫
          P.map (interMap U (fun a ↦ e (x a)) i.succAbove).op) :=
  (congrArg (((cechComplexFunctor U).obj P).d n (n + 1) ≫ ·)
      (fwd_comp_π U P e (n + 1) x)).trans (d_comp_π U P n (fun a ↦ e (x a)))

/-- **The comparison map commutes with the Čech differentials.** -/
theorem fwd_comm (n : ℕ) :
    fwd U P e n ≫ ((cechComplexFunctor (fun i ↦ U (e i))).obj P).d n (n + 1) =
      ((cechComplexFunctor U).obj P).d n (n + 1) ≫ fwd U P e (n + 1) :=
  hom_ext (fun i ↦ U (e i)) P fun x ↦ by
    rw [Category.assoc, Category.assoc]
    exact (fwd_comp_d_comp_π U P e n x).trans (d_comp_fwd_comp_π U P e n x).symm

/-- **The Čech complexes of a family and of its reindexing along an equivalence are
isomorphic.** -/
noncomputable def cechIso :
    (cechComplexFunctor U).obj P ≅ (cechComplexFunctor (fun i ↦ U (e i))).obj P :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦
      { hom := fwd U P e n
        inv := bwd U P e n
        hom_inv_id := fwd_comp_bwd U P e n
        inv_hom_id := bwd_comp_fwd U P e n })
    (fun i j hij ↦ by
      obtain rfl : j = i + 1 := hij.symm
      exact fwd_comm U P e i)

/-- **Čech cohomology is invariant under reindexing the family along an equivalence.** If the
degree `n` Čech cohomology of `U` vanishes, so does that of the reindexed family. -/
theorem isZero_homology_of_reindex [CategoryWithHomology A] (n : ℕ)
    (h : IsZero (((cechComplexFunctor U).obj P).homology n)) :
    IsZero (((cechComplexFunctor (fun i ↦ U (e i))).obj P).homology n) :=
  h.of_iso
    ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) n).mapIso (cechIso U P e)).symm

end Stacks.CategoryTheory.CechReindex

end
