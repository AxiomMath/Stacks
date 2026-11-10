module

public import StacksFrontier.CategoryTheory.Sites.CechComplex
public import StacksFrontier.CategoryTheory.Sites.CechComplexAlternatingHomotopy

/-!
# Signed sorting on the Čech complex of a presheaf with values in a preadditive category

The signed sorting of tuples gives an endomorphism of the Čech complex of a presheaf with
values in a preadditive category, homotopic to the identity when the objects of the family are
subterminal (Stacks 01FM).

All names are in the namespace `Stacks.CategoryTheory.CechComplex.Sorting`.

## Main definitions

* `sortHom`: signed sorting, as an endomorphism of the Čech complex.

## Main results

* `sortHomotopy_identity`: in positive degree, the differential of the sorting homotopy plus the
  sorting homotopy of the differential is the identity minus signed sorting.
* `sortHomHomotopy`: signed sorting is homotopic to the identity of the Čech complex.

## References

* [Stacks Project, Tag 01FM](https://stacks.math.columbia.edu/tag/01FM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v' v u u'

namespace Stacks.CategoryTheory.CechComplex.Sorting

open Stacks.CategoryTheory.CechComplex
open Stacks.CategoryTheory.CechComplex.Alternating (Contained SupportedTuple SupportedChain boundary
  projection chainHomotopy chainMap faceTuple isSubterminal_inter)

noncomputable section

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {ι : Type w} [LinearOrder ι]
  (U : ι → C) {A : Type u'} [Category.{v'} A] [Preadditive A] [HasProducts.{w} A]
  (P : Cᵒᵖ ⥤ A)

/-- **Evaluation of a supported chain** against the Čech complex: a formal combination of tuples
`t` whose intersection receives a morphism from `V` is sent to the corresponding combination of
the projections onto the factors `P(inter U t)`, each followed by restriction to `V`. -/
def eval (V : C) (p : ℕ) :
    SupportedChain U V p →+ (((cechComplexFunctor U).obj P).X p ⟶ P.obj (op V)) :=
  FreeAbelianGroup.lift fun t => π U P p t.1 ≫ P.map t.2.hom.op

omit [LinearOrder ι] in
/-- Evaluation of a single supported tuple `t` is the projection onto `P(inter U t)` followed by
restriction to `V`. -/
theorem eval_of (V : C) (p : ℕ) (t : SupportedTuple U V p) :
    eval U P V p (FreeAbelianGroup.of t) = π U P p t.1 ≫ P.map t.2.hom.op :=
  FreeAbelianGroup.lift_apply_of _ _

variable (hU : ∀ i, IsSubterminal (U i))

omit [LinearOrder ι] in
include hU in
/-- The differential, followed by evaluation, is evaluation of the boundary. -/
theorem d_comp_eval (V : C) (p : ℕ) (a : SupportedChain U V (p + 1)) :
    ((cechComplexFunctor U).obj P).d p (p + 1) ≫ eval U P V (p + 1) a =
      eval U P V p (boundary U V p a) := by
  induction a using FreeAbelianGroup.induction_on with
  | zero => simp
  | of t =>
    rw [eval_of, ← Category.assoc, d_comp_π, Preadditive.sum_comp, Alternating.boundary,
      FreeAbelianGroup.lift_apply_of, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, eval_of, Preadditive.zsmul_comp, Category.assoc, ← Functor.map_comp, ← op_comp]
    congr 4
    exact isSubterminal_inter U hU _ _ _
  | neg a ha => simp [ha]
  | add a b ha hb => simp [ha, hb, Preadditive.comp_add]

omit [LinearOrder ι] in
include hU in
/-- Evaluation is compatible with shrinking the supporting object. -/
theorem eval_chainMap {V W : C} (h : Contained V W) (p : ℕ) (a : SupportedChain U W p) :
    eval U P V p (chainMap U h p a) = eval U P W p a ≫ P.map h.hom.op := by
  induction a using FreeAbelianGroup.induction_on with
  | zero => simp
  | of t =>
    rw [Alternating.chainMap_of, eval_of, eval_of, Category.assoc, ← Functor.map_comp, ← op_comp]
    congr 4
    exact isSubterminal_inter U hU _ _ _
  | neg a ha => simp [ha]
  | add a b ha hb => simp [ha, hb, Preadditive.add_comp]

omit [LinearOrder ι] in
include hU in
/-- Evaluating the tautological tuple over its own intersection is the projection. -/
theorem eval_self (p : ℕ) (t : Fin (p + 1) → ι) :
    eval U P (inter U t) p (FreeAbelianGroup.of ⟨t, Contained.refl _⟩) = π U P p t := by
  rw [eval_of, Contained.hom_eq (isSubterminal_inter U hU t) _ (𝟙 _)]
  simp

/-- **Signed sorting**, as an endomorphism of a term of the Čech complex: the component at a
tuple `t` evaluates the signed sorting of `t` over the intersection `inter U t`. -/
def sortEnd (p : ℕ) :
    ((cechComplexFunctor U).obj P).X p ⟶ ((cechComplexFunctor U).obj P).X p :=
  lift U P fun t => eval U P (inter U t) p (projection U (inter U t) p
    (FreeAbelianGroup.of ⟨t, Contained.refl _⟩))

/-- **The sorting homotopy**, from degree `p + 1` to degree `p`: the component at a tuple `t`
evaluates the chain-level homotopy of `t` over the intersection `inter U t`. -/
def sortHomotopy (p : ℕ) :
    ((cechComplexFunctor U).obj P).X (p + 1) ⟶ ((cechComplexFunctor U).obj P).X p :=
  lift U P fun t => eval U P (inter U t) (p + 1) (chainHomotopy U (inter U t) p
    (FreeAbelianGroup.of ⟨t, Contained.refl _⟩))

/-- A map out of the Čech complex that is determined on the projections by a family of maps of
supported chains `F`, compatible with `chainMap`, is determined on all supported chains. -/
private theorem comp_eval_of_comp_π {ι : Type w} (U : ι → C) (hU : ∀ i, IsSubterminal (U i))
    {m p : ℕ}
    (g : ((cechComplexFunctor U).obj P).X m ⟶ ((cechComplexFunctor U).obj P).X p)
    (F : ∀ V, SupportedChain U V p →+ SupportedChain U V m)
    (hF : ∀ {V W : C} (h : Contained V W) (a : SupportedChain U W p),
      chainMap U h m (F W a) = F V (chainMap U h p a))
    (hg : ∀ t : Fin (p + 1) → ι, g ≫ π U P p t =
      eval U P (inter U t) m (F _ (FreeAbelianGroup.of ⟨t, Contained.refl _⟩)))
    (V : C) (a : SupportedChain U V p) :
    g ≫ eval U P V p a = eval U P V m (F V a) := by
  induction a using FreeAbelianGroup.induction_on with
  | zero => simp
  | of t =>
    have ht : FreeAbelianGroup.of t =
        chainMap U t.2 p (FreeAbelianGroup.of ⟨t.1, Contained.refl _⟩) :=
      rfl
    rw [ht, ← hF, eval_chainMap U P hU, eval_chainMap U P hU, ← Category.assoc,
      eval_self U P hU, hg]
  | neg a ha => simp [ha]
  | add a b ha hb => simp [ha, hb, Preadditive.comp_add]

include hU in
/-- Signed sorting, followed by evaluation, is evaluation of the signed sorting. -/
theorem sortEnd_comp_eval (V : C) (p : ℕ) (a : SupportedChain U V p) :
    sortEnd U P p ≫ eval U P V p a = eval U P V p (projection U V p a) :=
  comp_eval_of_comp_π P U hU _ (fun V => projection U V p)
    (fun h a => Alternating.chainMap_projection U h p a) (fun _ => lift_comp_π ..) V a

include hU in
/-- The sorting homotopy, followed by evaluation, is evaluation of the chain-level homotopy. -/
theorem sortHomotopy_comp_eval (V : C) (p : ℕ) (a : SupportedChain U V p) :
    sortHomotopy U P p ≫ eval U P V p a = eval U P V (p + 1) (chainHomotopy U V p a) :=
  comp_eval_of_comp_π P U hU _ (fun V => chainHomotopy U V p)
    (fun h a => Alternating.chainMap_homotopy U h p a) (fun _ => lift_comp_π ..) V a

include hU in
/-- Signed sorting commutes with the Čech differential. -/
theorem d_comp_sortEnd (p : ℕ) :
    ((cechComplexFunctor U).obj P).d p (p + 1) ≫ sortEnd U P (p + 1) =
      sortEnd U P p ≫ ((cechComplexFunctor U).obj P).d p (p + 1) := by
  refine hom_ext U P fun t => ?_
  rw [Category.assoc, sortEnd, lift_comp_π, d_comp_eval U P hU, Category.assoc,
    ← eval_self U P hU, d_comp_eval U P hU, sortEnd_comp_eval U P hU,
    Alternating.boundary_projection U hU]

include hU in
/-- **The cochain-level content of [Stacks, Tag 01FM], in a preadditive category.** In positive
degree the differential of the homotopy plus the homotopy of the differential is the identity
minus signed sorting. -/
theorem sortHomotopy_identity (p : ℕ) :
    ((cechComplexFunctor U).obj P).d (p + 1) (p + 2) ≫ sortHomotopy U P (p + 1) +
        sortHomotopy U P p ≫ ((cechComplexFunctor U).obj P).d p (p + 1) =
      𝟙 _ - sortEnd U P (p + 1) := by
  refine hom_ext U P fun t => ?_
  rw [Preadditive.add_comp, Preadditive.sub_comp, Category.id_comp, Category.assoc,
    sortHomotopy, lift_comp_π, d_comp_eval U P hU, Category.assoc, ← eval_self U P hU,
    d_comp_eval U P hU, sortHomotopy_comp_eval U P hU, ← map_add,
    Alternating.chainHomotopy_identity U hU, map_sub, sortEnd_comp_eval U P hU]

/-- In degree zero the sorting homotopy vanishes. -/
theorem sortHomotopy_zero : sortHomotopy U P 0 = 0 := by
  refine hom_ext U P fun t => ?_
  rw [sortHomotopy, lift_comp_π, zero_comp]
  change eval U P (inter U t) 1
    ((0 : SupportedChain U (inter U t) 0 →+ SupportedChain U (inter U t) 1) _) = 0
  rw [AddMonoidHom.zero_apply, map_zero]

include hU in
/-- In degree zero signed sorting is the identity. -/
theorem sortEnd_zero : sortEnd U P 0 = 𝟙 _ := by
  refine hom_ext U P fun t => ?_
  rw [sortEnd, lift_comp_π, Alternating.projection_zero, eval_self U P hU, Category.id_comp]

/-- In degree `p`, signed sorting vanishes as soon as the tuples of length `p + 1` are all
non-injective, which happens once `p + 1` exceeds the number of indices. -/
theorem sortEnd_eq_zero [Fintype ι] (p : ℕ) (hp : Fintype.card ι < p + 1) :
    sortEnd U P p = 0 := by
  refine hom_ext U P fun t => ?_
  have hni : ¬ Function.Injective t := fun h =>
    absurd (Fintype.card_le_of_injective t h) (by simpa using hp)
  rw [sortEnd, lift_comp_π, zero_comp, Alternating.projection, FreeAbelianGroup.lift_apply_of,
    dite_eq_right hni, map_zero]

/-- **Signed sorting, as an endomorphism of the Čech complex.** -/
def sortHom : (cechComplexFunctor U).obj P ⟶ (cechComplexFunctor U).obj P where
  f := sortEnd U P
  comm' i j hij := by
    change i + 1 = j at hij
    subst hij
    exact (d_comp_sortEnd U P hU i).symm

/-- The component of `sortHom` in degree `p` is `sortEnd`. -/
@[simp]
theorem sortHom_f (p : ℕ) : (sortHom U P hU).f p = sortEnd U P p := rfl

/-- The components of the sorting homotopy, indexed as `Homotopy` expects. -/
def sortHomotopyComponent (i j : ℕ) :
    ((cechComplexFunctor U).obj P).X i ⟶ ((cechComplexFunctor U).obj P).X j :=
  if h : j + 1 = i then h ▸ sortHomotopy U P j else 0

/-- The component of the sorting homotopy from degree `j + 1` to degree `j` is `sortHomotopy`. -/
theorem sortHomotopyComponent_succ (j : ℕ) :
    sortHomotopyComponent U P (j + 1) j = sortHomotopy U P j := by
  simp only [sortHomotopyComponent, dite_true]

/-- **[Stacks, Tag 01FM] in a preadditive category, chain-level form.** Signed sorting is
homotopic to the identity of the Čech complex of a presheaf with values in a preadditive
category, for a family of subterminal objects. -/
def sortHomHomotopy : Homotopy (sortHom U P hU) (𝟙 ((cechComplexFunctor U).obj P)) := by
  refine Homotopy.symm
    { hom := sortHomotopyComponent U P, zero := fun _ _ h => dite_eq_right h, comm := fun i => ?_ }
  rw [Homotopy.dNext_cochainComplex, sortHomotopyComponent_succ, sortHom_f,
    HomologicalComplex.id_f]
  cases i with
  | zero =>
    rw [Homotopy.prevD_zero_cochainComplex, add_zero, sortEnd_zero U P hU,
      sortHomotopy_zero, comp_zero, zero_add]
  | succ p =>
    rw [Homotopy.prevD_succ_cochainComplex, sortHomotopyComponent_succ,
      sortHomotopy_identity U P hU p, sub_add_cancel]

end

end Stacks.CategoryTheory.CechComplex.Sorting
