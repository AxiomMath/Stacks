module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.KoszulContraction

/-!
# The Leibniz rule for the Koszul contraction

Let `X` be a topological space with a sheaf of commutative rings `𝒪`, let `F` be a sheaf of
`𝒪`-modules with an exterior algebra `⋀(F)`, and let `φ : F ⟶ 𝒪`. The Koszul contraction
`ι_φ : ⋀^{k+1} F ⟶ ⋀^k F` of `SheafOfModules.exteriorContraction` is a derivation of degree
`-1`: for a local section `g` of `⋀^{k+1} F` and a local section `e` of `F`,

`ι_φ(g ∧ e) = ι_φ(g) ∧ e + (-1)^{k+1} φ(e) · g`.

## Main results

* `SheafOfModules.exteriorContraction_mul_gen`: the Leibniz rule above, on local sections.

## Implementation notes

Sections of a sheafified exterior power are only locally wedges of sections, so the rule is
proved germwise. The defect `ι_φ(g ∧ e) - ι_φ(g) ∧ e - (-1)^{k+1} φ(e) · g` commutes with
restriction; every germ of `⋀^{k+1} F` is a germ of a section of the presheaf of sectionwise
exterior powers (`SheafOfModules.exists_stalkMapL_extPowCmp_eq`); on such a section the defect is
linear, and on a wedge of local sections `s₀ ∧ ⋯ ∧ s_k` the comparison of Tag 01CG turns the
product with `e` into the wedge `s₀ ∧ ⋯ ∧ s_k ∧ e`, whose contraction is the alternating sum of
`SheafOfModules.extPowCmp_app_exteriorContraction_ιMulti`. Splitting off the last term of that
sum is the rule.

The product with `e` is taken on the right, so that the degrees `(k + 1) + 1` and `k + 2` agree
definitionally, as for `Stacks.GradedAlgebra.homogeneousProd`.

## References

* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf Opposite TopologicalSpace
open scoped ExteriorAlgebra

universe u

namespace SheafOfModules

section Leibniz

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {M : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (A : GradedAlgebra.{u, u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp))
  (gen : M ⟶ A.piece 1) (hA : GradedAlgebra.IsExteriorAlgebra A gen)
  (φ : M ⟶ SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Osharp))

/-- The comparison of Tag 01CG on a wedge of local sections is the ordered product of their
generators. -/
theorem extPowCmp_app_ιMulti (n : ℕ) (V : Opens ↥X) (s : Fin n → M.val.obj (op V)) :
    (A.extPowCmp (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property) gen hA.1
        n).app (op V)
        (exteriorPower.ιMulti ((Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op V)) n s) =
      A.toPresheafGradedAlgebra.homogeneousProd (op V) n fun i => gen.val.app (op V) (s i) :=
  Stacks.GradedAlgebra.extCmpSections_ιMulti A.toPresheafGradedAlgebra gen.val
    (fun Y y => hA.1 Y y) n (op V) s

/-- The ordered product of a family extended on the right by `e` is the ordered product of the
family, multiplied on the right by `e`. -/
theorem homogeneousProd_snoc (n : ℕ) (V : Opens ↥X) (s : Fin n → M.val.obj (op V))
    (e : M.val.obj (op V)) :
    A.toPresheafGradedAlgebra.homogeneousProd (op V) (n + 1)
        (fun i => gen.val.app (op V) ((Fin.snoc s e : Fin (n + 1) → M.val.obj (op V)) i)) =
      (A.mul (n : ℤ) 1).app (op V)
        (A.toPresheafGradedAlgebra.homogeneousProd (op V) n fun i => gen.val.app (op V) (s i))
        (gen.val.app (op V) e) := by
  change (A.mul (n : ℤ) 1).app (op V)
      (A.toPresheafGradedAlgebra.homogeneousProd (op V) n
        fun i => gen.val.app (op V) ((Fin.snoc s e : Fin (n + 1) → M.val.obj (op V)) i.castSucc))
      (gen.val.app (op V) ((Fin.snoc s e : Fin (n + 1) → M.val.obj (op V)) (Fin.last n))) = _
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- Removing an entry other than the last from a family extended on the right by `e` is
extending the shortened family by `e`. -/
theorem snoc_comp_castSucc_succAbove {α : Type*} {n : ℕ} (s : Fin (n + 1) → α) (e : α)
    (i : Fin (n + 1)) :
    (fun j => (Fin.snoc s e : Fin (n + 2) → α) ((Fin.castSucc i).succAbove j)) =
      Fin.snoc (fun j => s (i.succAbove j)) e := by
  funext j
  refine Fin.lastCases ?_ (fun j' => ?_) j
  · rw [Fin.succAbove_ne_last_last (Fin.castSucc_lt_last i).ne, Fin.snoc_last, Fin.snoc_last]
  · rw [Fin.castSucc_succAbove_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]

/-- The comparison of Tag 01CG turns the product of a wedge with a generator on the right into
the wedge of the extended family. -/
theorem mul_gen_extPowCmp_ιMulti (n : ℕ) (V : Opens ↥X) (s : Fin n → M.val.obj (op V))
    (e : M.val.obj (op V)) :
    (A.mul (n : ℤ) 1).app (op V)
        ((A.extPowCmp (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property) gen hA.1
            n).app (op V)
                (exteriorPower.ιMulti ((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj (op V)) n s))
        (gen.val.app (op V) e) =
      (A.extPowCmp (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property) gen hA.1
          (n + 1)).app (op V)
        (exteriorPower.ιMulti ((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj (op V)) (n + 1)
          (Fin.snoc s e : Fin (n + 1) → M.val.obj (op V))) := by
  refine Eq.trans ?_ (extPowCmp_app_ιMulti A gen hA (n + 1) V _).symm
  refine Eq.trans ?_ (homogeneousProd_snoc A gen n V s e).symm
  exact congrArg (fun z => (A.mul (n : ℤ) 1).app (op V) z (gen.val.app (op V) e))
    (extPowCmp_app_ιMulti A gen hA n V s)

/-- The comparison of Tag 01CG commutes with scalar multiplication of a wedge, whose scalar and
family may be rewritten along equalities. -/
private theorem extPowCmp_app_smul_ιMulti_congr (n : ℕ) (V : Opens ↥X)
    (c c' : (Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
    (f f' : Fin n → M.val.obj (op V)) (hc : c = c') (hf : f = f') :
    (A.extPowCmp (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property) gen hA.1
        n).app (op V)
        (c • exteriorPower.ιMulti ((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj (op V)) n f) =
      c' • (A.extPowCmp (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property) gen
        hA.1 n).app (op V)
        (exteriorPower.ιMulti ((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj (op V)) n f') := by
  subst hc hf
  exact map_smul _ _ _

/-- A term of the contraction of a wedge extended by `e`, at an entry other than the last. -/
theorem extPowCmp_contraction_term_castSucc (k : ℕ) (V : Opens ↥X)
    (s : Fin (k + 1) → M.val.obj (op V)) (e : M.val.obj (op V)) (j : Fin (k + 1)) :
    (A.extPowCmp (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property) gen hA.1
        (k + 1)).app (op V)
        (((-1 : ((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj (op V))) ^ (j.castSucc : ℕ) *
            unitDualApp φ (op V) ((Fin.snoc s e : Fin (k + 1 + 1) → M.val.obj (op V)) j.castSucc)) •
          exteriorPower.ιMulti ((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj (op V)) (k + 1)
            fun i => (Fin.snoc s e : Fin (k + 1 + 1) → M.val.obj (op V)) (j.castSucc.succAbove i)) =
      ((-1 : ((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj (op V))) ^ (j : ℕ) * unitDualApp φ
          (op V) (s j)) •
        (A.mul (k : ℤ) 1).app (op V)
          ((A.extPowCmp (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property) gen hA.1
              k).app (op V)
                  (exteriorPower.ιMulti ((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj (op V)) k
                      fun i => s (j.succAbove i)))
          (gen.val.app (op V) e) := by
  refine (extPowCmp_app_smul_ιMulti_congr A gen hA (k + 1) V _ _ _ _
    (by rw [Fin.val_castSucc, Fin.snoc_castSucc])
    (snoc_comp_castSucc_succAbove s e j)).trans ?_
  exact congrArg (_ • ·) (mul_gen_extPowCmp_ιMulti A gen hA k V _ e).symm

/-- The last term of the contraction of a wedge extended by `e`. -/
theorem extPowCmp_contraction_term_last (k : ℕ) (V : Opens ↥X)
    (s : Fin (k + 1) → M.val.obj (op V)) (e : M.val.obj (op V)) :
    (A.extPowCmp (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property) gen hA.1
        (k + 1)).app (op V)
        (((-1 : ((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj (op V))) ^
            ((Fin.last (k + 1) : Fin (k + 1 + 1)) : ℕ) *
            unitDualApp φ (op V)
              ((Fin.snoc s e : Fin (k + 1 + 1) → M.val.obj (op V)) (Fin.last (k + 1)))) •
          exteriorPower.ιMulti ((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj (op V)) (k + 1)
            fun i => (Fin.snoc s e : Fin (k + 1 + 1) → M.val.obj (op V))
              ((Fin.last (k + 1)).succAbove i)) =
      ((-1 : ((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj (op V))) ^ (k + 1) * unitDualApp φ
          (op V) e) •
        (A.extPowCmp (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property) gen hA.1
            (k + 1)).app (op V)
                (exteriorPower.ιMulti ((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
                    (k + 1) s) := by
  exact extPowCmp_app_smul_ιMulti_congr A gen hA (k + 1) V _ _ _ _
    (by rw [Fin.val_last, Fin.snoc_last])
    (funext fun i => by rw [Fin.succAbove_last_apply, Fin.snoc_castSucc])

/-- The contraction of a wedge, multiplied on the right by `e`, as a sum. -/
theorem mul_gen_exteriorContraction_extPowCmp_ιMulti (k : ℕ) (V : Opens ↥X)
    (s : Fin (k + 1) → M.val.obj (op V)) (e : M.val.obj (op V)) :
    (A.mul (k : ℤ) 1).app (op V)
        ((exteriorContraction M A gen hA φ k).val.app (op V)
          ((A.extPowCmp (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property) gen hA.1
              (k + 1)).app (op V)
                  (exteriorPower.ιMulti ((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
                      (k + 1) s)))
        (gen.val.app (op V) e) =
      ∑ j : Fin (k + 1),
          ((-1 : ((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj (op V))) ^ (j : ℕ) * unitDualApp φ
              (op V) (s j)) •
        (A.mul (k : ℤ) 1).app (op V)
          ((A.extPowCmp (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property) gen hA.1
              k).app (op V)
                  (exteriorPower.ιMulti ((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj (op V)) k
                      fun i => s (j.succAbove i)))
          (gen.val.app (op V) e) := by
  refine Eq.trans (congrArg (fun z => (A.mul (k : ℤ) 1).app (op V) z (gen.val.app (op V) e))
    (extPowCmp_app_exteriorContraction_ιMulti M A gen hA φ k (op V) s)) ?_
  refine Eq.trans (congrArg (fun z => (A.mul (k : ℤ) 1).app (op V) z (gen.val.app (op V) e))
    (map_sum _ _ _)) ?_
  refine Eq.trans (congrArg (fun f : (A.piece (1 : ℤ)).val.obj (op V) →+
      (A.piece ((k : ℤ) + 1)).val.obj (op V) => f (gen.val.app (op V) e))
      (map_sum ((A.mul (k : ℤ) 1).app (op V)) _ _)) ?_
  refine Eq.trans (AddMonoidHom.finsetSum_apply _ _ _) ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Eq.trans (congrArg (fun z => (A.mul (k : ℤ) 1).app (op V) z (gen.val.app (op V) e))
    (map_smul _ _ _)) ?_
  exact (A.mul (k : ℤ) 1).map_smul_left (op V) _ _ _

/-- **The Leibniz rule on a wedge of local sections.** -/
theorem exteriorContraction_mul_gen_ιMulti (k : ℕ) (V : Opens ↥X)
    (s : Fin (k + 1) → M.val.obj (op V)) (e : M.val.obj (op V)) :
    (exteriorContraction M A gen hA φ (k + 1)).val.app (op V)
        ((A.mul ((k + 1 : ℕ) : ℤ) 1).app (op V)
          ((A.extPowCmp (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property) gen hA.1
              (k + 1)).app (op V)
                  (exteriorPower.ιMulti ((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
                      (k + 1) s))
          (gen.val.app (op V) e)) =
      (show (A.piece ((k + 1 : ℕ) : ℤ)).val.obj (op V) from (A.mul (k : ℤ) 1).app (op V)
          ((exteriorContraction M A gen hA φ k).val.app (op V)
            ((A.extPowCmp (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property) gen
                hA.1 (k + 1)).app (op V)
                    (exteriorPower.ιMulti ((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
                        (k + 1) s)))
          (gen.val.app (op V) e)) +
        ((-1 : ((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj (op V))) ^ (k + 1) * unitDualApp φ
            (op V) e) •
          (A.extPowCmp (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property) gen hA.1
              (k + 1)).app (op V)
                  (exteriorPower.ιMulti ((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
                      (k + 1) s) := by
  refine Eq.trans (congrArg (fun z => (exteriorContraction M A gen hA φ (k + 1)).val.app (op V) z)
    (mul_gen_extPowCmp_ιMulti A gen hA (k + 1) V s e)) ?_
  refine Eq.trans (extPowCmp_app_exteriorContraction_ιMulti M A gen hA φ (k + 1) (op V) _) ?_
  refine Eq.trans (map_sum _ _ _) ?_
  refine Eq.trans (Fin.sum_univ_castSucc _) ?_
  refine congrArg₂ (· + ·) ((Finset.sum_congr rfl fun j _ =>
    extPowCmp_contraction_term_castSucc A gen hA φ k V s e j).trans
      (mul_gen_exteriorContraction_extPowCmp_ιMulti A gen hA φ k V s e).symm)
    (extPowCmp_contraction_term_last A gen hA φ k V s e)

/-- The defect of the Leibniz rule at a local section `g` of `⋀^{k+1} F` and a local section
`e` of `F`: `ι_φ(g ∧ e) - ι_φ(g) ∧ e - (-1)^{k+1} φ(e) · g`. -/
noncomputable def leibnizDefect (k : ℕ) (U : Opens ↥X)
    (g : (A.piece ((k + 1 : ℕ) : ℤ)).val.obj (op U)) (e : M.val.obj (op U)) :
    (A.piece ((k + 1 : ℕ) : ℤ)).val.obj (op U) :=
  (exteriorContraction M A gen hA φ (k + 1)).val.app (op U)
      ((A.mul ((k + 1 : ℕ) : ℤ) 1).app (op U) g (gen.val.app (op U) e)) -
    (show (A.piece ((k + 1 : ℕ) : ℤ)).val.obj (op U) from (A.mul (k : ℤ) 1).app (op U)
        ((exteriorContraction M A gen hA φ k).val.app (op U) g) (gen.val.app (op U) e)) -
    ((-1 : ((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj (op U))) ^ (k + 1) * unitDualApp φ (op U)
        e) • g

/-- The defect vanishes on the image of a wedge of local sections. -/
theorem leibnizDefect_extPowCmp_ιMulti (k : ℕ) (V : Opens ↥X)
    (s : Fin (k + 1) → M.val.obj (op V)) (e : M.val.obj (op V)) :
    leibnizDefect A gen hA φ k V
      ((A.extPowCmp (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property) gen hA.1
          (k + 1)).app (op V)
              (exteriorPower.ιMulti ((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj (op V)) (k + 1)
                  s)) e = 0 := by
  unfold leibnizDefect
  rw [exteriorContraction_mul_gen_ιMulti A gen hA φ k V s e, sub_sub, sub_self]

/-- Multiplication on the right by a degree-one generator, as a linear map. -/
noncomputable def mulGenLinear (n : ℕ) (U : Opens ↥X) (e : M.val.obj (op U)) :
    (A.piece (n : ℤ)).val.obj (op U)
        →ₗ[((toRingCat (Opens.grothendieckTopology ↥X) Osharp).obj.obj (op U))]
            (A.piece ((n + 1 : ℕ) : ℤ)).val.obj (op U) where
  toFun g := (A.mul (n : ℤ) 1).app (op U) g (gen.val.app (op U) e)
  map_add' g g' := by
    change (A.mul (n : ℤ) 1).app (op U) (g + g') _ = _
    rw [map_add, AddMonoidHom.add_apply]
  map_smul' c g := (A.mul (n : ℤ) 1).map_smul_left (op U) c g _

/-- The defect of the Leibniz rule, as a linear map in the section of the exterior power. -/
noncomputable def leibnizDefectLinear (k : ℕ) (U : Opens ↥X) (e : M.val.obj (op U)) :
    (A.piece ((k + 1 : ℕ) : ℤ)).val.obj (op U)
        →ₗ[((toRingCat (Opens.grothendieckTopology ↥X) Osharp).obj.obj (op U))]
      (A.piece ((k + 1 : ℕ) : ℤ)).val.obj (op U) :=
  ((exteriorContraction M A gen hA φ (k + 1)).val.app (op U)).hom ∘ₗ
      mulGenLinear A gen (k + 1) U e -
    mulGenLinear A gen k U e ∘ₗ ((exteriorContraction M A gen hA φ k).val.app (op U)).hom -
    ((-1 : ((toRingCat (Opens.grothendieckTopology ↥X) Osharp).obj.obj (op U))) ^ (k + 1) *
        unitDualApp φ (op U) e) • LinearMap.id

/-- The defect as a linear map, on a section. -/
theorem leibnizDefectLinear_apply (k : ℕ) (U : Opens ↥X) (e : M.val.obj (op U))
    (g : (A.piece ((k + 1 : ℕ) : ℤ)).val.obj (op U)) :
    leibnizDefectLinear A gen hA φ k U e g = leibnizDefect A gen hA φ k U g e := rfl

/-- The defect vanishes on the image of the presheaf of sectionwise exterior powers. -/
theorem leibnizDefect_extPowCmp (k : ℕ) (V : Opens ↥X)
    (z : ⋀[((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj (op V))]^(k + 1) (M.val.obj (op V)))
        (e : M.val.obj (op V)) :
    leibnizDefect A gen hA φ k V
        ((A.extPowCmp (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property) gen hA.1
            (k + 1)).app (op V) z) e = 0 := by
  have h : leibnizDefectLinear A gen hA φ k V e ∘ₗ
      ((A.extPowCmp (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property) gen hA.1
          (k + 1)).app (op V)).hom = 0 := by
    refine exteriorPower.linearMap_ext (AlternatingMap.ext fun s => ?_)
    exact leibnizDefect_extPowCmp_ιMulti A gen hA φ k V s e
  exact LinearMap.congr_fun h z

/-- Multiplication on the right by a generator commutes with restriction. -/
theorem mul_gen_map (n : ℤ) {U W : Opens ↥X} (i : W ⟶ U)
    (g : (A.piece n).val.obj (op U)) (e : M.val.obj (op U)) :
    (A.piece (n + 1)).val.map i.op ((A.mul n 1).app (op U) g (gen.val.app (op U) e)) =
      (A.mul n 1).app (op W) ((A.piece n).val.map i.op g) (gen.val.app (op W) (M.val.map i.op e)) :=
  ((A.mul n 1).naturality i.op g (gen.val.app (op U) e)).trans
    (congrArg (fun y => (A.mul n 1).app (op W) ((A.piece n).val.map i.op g) y)
      (PresheafOfModules.naturality_apply gen.val i.op e).symm)

/-- The first term of the defect commutes with restriction. -/
theorem leibnizDefect_map_first (k : ℕ) {U W : Opens ↥X} (i : W ⟶ U)
    (g : (A.piece ((k + 1 : ℕ) : ℤ)).val.obj (op U)) (e : M.val.obj (op U)) :
    (A.piece ((k + 1 : ℕ) : ℤ)).val.map i.op
        ((exteriorContraction M A gen hA φ (k + 1)).val.app (op U)
          ((A.mul ((k + 1 : ℕ) : ℤ) 1).app (op U) g (gen.val.app (op U) e))) =
      (exteriorContraction M A gen hA φ (k + 1)).val.app (op W)
        ((A.mul ((k + 1 : ℕ) : ℤ) 1).app (op W) ((A.piece ((k + 1 : ℕ) : ℤ)).val.map i.op g)
          (gen.val.app (op W) (M.val.map i.op e))) :=
  (PresheafOfModules.naturality_apply (exteriorContraction M A gen hA φ (k + 1)).val i.op
      _).symm.trans
    (congrArg (fun y => (exteriorContraction M A gen hA φ (k + 1)).val.app (op W) y)
      (mul_gen_map A gen ((k + 1 : ℕ) : ℤ) i g e))

/-- The second term of the defect commutes with restriction. -/
theorem leibnizDefect_map_second (k : ℕ) {U W : Opens ↥X} (i : W ⟶ U)
    (g : (A.piece ((k + 1 : ℕ) : ℤ)).val.obj (op U)) (e : M.val.obj (op U)) :
    (A.piece ((k : ℤ) + 1)).val.map i.op
        ((A.mul (k : ℤ) 1).app (op U)
          ((exteriorContraction M A gen hA φ k).val.app (op U) g) (gen.val.app (op U) e)) =
      (A.mul (k : ℤ) 1).app (op W)
        ((exteriorContraction M A gen hA φ k).val.app (op W)
          ((A.piece ((k + 1 : ℕ) : ℤ)).val.map i.op g))
        (gen.val.app (op W) (M.val.map i.op e)) :=
  (mul_gen_map A gen (k : ℤ) i _ e).trans
    (congrArg (fun y => (A.mul (k : ℤ) 1).app (op W) y (gen.val.app (op W) (M.val.map i.op e)))
      (PresheafOfModules.naturality_apply (exteriorContraction M A gen hA φ k).val i.op g).symm)

/-- The third term of the defect commutes with restriction. -/
theorem leibnizDefect_map_third (k : ℕ) {U W : Opens ↥X} (i : W ⟶ U)
    (g : (A.piece ((k + 1 : ℕ) : ℤ)).val.obj (op U)) (e : M.val.obj (op U)) :
    (A.piece ((k + 1 : ℕ) : ℤ)).val.map i.op
        (((-1 : ((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj (op U))) ^ (k + 1) * unitDualApp φ
            (op U) e) • g) =
      ((-1 : ((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj (op W))) ^ (k + 1) * unitDualApp φ
          (op W) (M.val.map i.op e)) •
        (A.piece ((k + 1 : ℕ) : ℤ)).val.map i.op g := by
  refine Eq.trans (PresheafOfModules.map_smul _ i.op _ g) ?_
  refine congrArg (fun c => c • (A.piece ((k + 1 : ℕ) : ℤ)).val.map i.op g) ?_
  rw [map_mul, map_pow, map_neg, map_one]
  exact congrArg
      (fun c => (-1 : ((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj (op W))) ^ (k + 1) * c)
    (PresheafOfModules.naturality_apply φ.val i.op e).symm

/-- The defect commutes with restriction. -/
theorem leibnizDefect_map (k : ℕ) {U W : Opens ↥X} (i : W ⟶ U)
    (g : (A.piece ((k + 1 : ℕ) : ℤ)).val.obj (op U)) (e : M.val.obj (op U)) :
    (A.piece ((k + 1 : ℕ) : ℤ)).val.map i.op (leibnizDefect A gen hA φ k U g e) =
      leibnizDefect A gen hA φ k W ((A.piece ((k + 1 : ℕ) : ℤ)).val.map i.op g)
        (M.val.map i.op e) := by
  refine Eq.trans (map_sub _ _ _) ?_
  refine congrArg₂ (· - ·) ?_ (leibnizDefect_map_third A φ k i g e)
  refine Eq.trans (map_sub _ _ _) ?_
  exact congrArg₂ (· - ·) (leibnizDefect_map_first A gen hA φ k i g e)
    (leibnizDefect_map_second A gen hA φ k i g e)

/-- **The defect of the Leibniz rule vanishes.** Germwise, a section of `⋀^{k+1} F` is the image
of a section of the presheaf of sectionwise exterior powers, where the defect vanishes, and the
defect commutes with restriction. -/
theorem leibnizDefect_eq_zero (k : ℕ) (U : Opens ↥X)
    (g : (A.piece ((k + 1 : ℕ) : ℤ)).val.obj (op U)) (e : M.val.obj (op U)) :
    leibnizDefect A gen hA φ k U g e = 0 := by
  refine TopCat.Presheaf.section_ext
    ((AlgebraicGeometry.SheafOfModules.toTopSheaf _).obj (A.piece ((k + 1 : ℕ) : ℤ))) U _ 0
    fun x hx => ?_
  obtain ⟨t, ht⟩ := exists_stalkMapL_extPowCmp_eq A gen hA (k + 1) x
    (TopCat.Presheaf.germ (A.piece ((k + 1 : ℕ) : ℤ)).val.presheaf U x hx g)
  obtain ⟨V, hxV, z, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ t
  have ht' := (PresheafOfModules.stalkMapL_germ x _ V hxV z).symm.trans ht
  obtain ⟨W, hxW, iV, iU, hW⟩ := TopCat.Presheaf.germ_eq _ x hxV hx _ _ ht'
  have hz : (A.piece ((k + 1 : ℕ) : ℤ)).val.map iU.op g =
      (A.extPowCmp (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property) gen hA.1
          (k + 1)).app (op W) ((PresheafOfModules.extPow (k + 1) M.val).map iV.op z) :=
    hW.symm.trans
        (PresheafOfModules.naturality_apply
            (A.extPowCmp (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property) gen
                hA.1 (k + 1)) iV.op z).symm
  let P := ((AlgebraicGeometry.SheafOfModules.toTopSheaf _).obj
    (A.piece ((k + 1 : ℕ) : ℤ))).presheaf
  have h0 : leibnizDefect A gen hA φ k W
      ((A.piece ((k + 1 : ℕ) : ℤ)).val.map iU.op g) (M.val.map iU.op e) = 0 :=
    (congrArg (fun y => leibnizDefect A gen hA φ k W y (M.val.map iU.op e)) hz).trans
      (leibnizDefect_extPowCmp A gen hA φ k W _ _)
  refine Eq.trans (TopCat.Presheaf.germ_res_apply P iU x hxW _).symm ?_
  refine Eq.trans (congrArg (P.germ W x hxW) ((leibnizDefect_map A gen hA φ k iU g e).trans h0)) ?_
  exact (map_zero _).trans (map_zero _).symm

/-- **The Leibniz rule for the Koszul contraction**: for a local section `g` of `⋀^{k+1} F` and a
local section `e` of `F`, `ι_φ(g ∧ e) = ι_φ(g) ∧ e + (-1)^{k+1} φ(e) · g`. -/
theorem exteriorContraction_mul_gen (k : ℕ) (U : Opens ↥X)
    (g : (A.piece ((k + 1 : ℕ) : ℤ)).val.obj (op U)) (e : M.val.obj (op U)) :
    (exteriorContraction M A gen hA φ (k + 1)).val.app (op U)
        ((A.mul ((k + 1 : ℕ) : ℤ) 1).app (op U) g (gen.val.app (op U) e)) =
      (show (A.piece ((k + 1 : ℕ) : ℤ)).val.obj (op U) from (A.mul (k : ℤ) 1).app (op U)
          ((exteriorContraction M A gen hA φ k).val.app (op U) g) (gen.val.app (op U) e)) +
        ((-1 : ((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj (op U))) ^ (k + 1) *
          unitDualApp φ (op U) e) • g := by
  have h := leibnizDefect_eq_zero A gen hA φ k U g e
  unfold leibnizDefect at h
  rwa [sub_sub, sub_eq_zero] at h

/-- **The Leibniz rule when `φ(e) = 0`**: `ι_φ(g ∧ e) = ι_φ(g) ∧ e`. -/
theorem exteriorContraction_mul_gen_of_unitDualApp_eq_zero (k : ℕ) (U : Opens ↥X)
    (g : (A.piece ((k + 1 : ℕ) : ℤ)).val.obj (op U)) (e : M.val.obj (op U))
    (he : unitDualApp φ (op U) e = 0) :
    (exteriorContraction M A gen hA φ (k + 1)).val.app (op U)
        ((A.mul ((k + 1 : ℕ) : ℤ) 1).app (op U) g (gen.val.app (op U) e)) =
      (show (A.piece ((k + 1 : ℕ) : ℤ)).val.obj (op U) from (A.mul (k : ℤ) 1).app (op U)
          ((exteriorContraction M A gen hA φ k).val.app (op U) g) (gen.val.app (op U) e)) :=
  (exteriorContraction_mul_gen A gen hA φ k U g e).trans
    ((congrArg (_ + ·) (smul_eq_zero_of_left (mul_eq_zero_of_right _ he) g)).trans (add_zero _))

/-- **The Leibniz rule when `ι_φ(g) = 0`**: `ι_φ((-1)^{k+1} g ∧ e) = φ(e) · g`. -/
theorem exteriorContraction_mul_gen_of_eq_zero (k : ℕ) (U : Opens ↥X)
    (g : (A.piece ((k + 1 : ℕ) : ℤ)).val.obj (op U)) (e : M.val.obj (op U))
    (hg : (exteriorContraction M A gen hA φ k).val.app (op U) g = 0) :
    (exteriorContraction M A gen hA φ (k + 1)).val.app (op U)
        ((A.mul ((k + 1 : ℕ) : ℤ) 1).app (op U) ((((k : ℤ) + 1).negOnePow : ℤ) • g)
          (gen.val.app (op U) e)) = unitDualApp φ (op U) e • g := by
  have h1 : (A.mul ((k + 1 : ℕ) : ℤ) 1).app (op U) ((((k : ℤ) + 1).negOnePow : ℤ) • g)
      (gen.val.app (op U) e) = (((k : ℤ) + 1).negOnePow : ℤ) •
        (A.mul ((k + 1 : ℕ) : ℤ) 1).app (op U) g (gen.val.app (op U) e) := by
    rw [map_zsmul ((A.mul ((k + 1 : ℕ) : ℤ) 1).app (op U)), AddMonoidHom.zsmul_apply]
  have h2 := exteriorContraction_mul_gen A gen hA φ k U g e
  have h3 : (A.mul (k : ℤ) 1).app (op U)
      ((exteriorContraction M A gen hA φ k).val.app (op U) g) (gen.val.app (op U) e) = 0 := by
    rw [hg, map_zero, AddMonoidHom.zero_apply]
  have hε : ((((k : ℤ) + 1).negOnePow : ℤ) : (Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj
      (op U)) * (-1 : ((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj (op U))) ^ (k + 1) = 1 := by
    rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, Int.coe_negOnePow_natCast,
      Int.cast_pow, Int.cast_neg, Int.cast_one, ← mul_pow, neg_one_mul, neg_neg, one_pow]
  refine (congrArg _ h1).trans ?_
  refine (map_zsmul _ _ _).trans ?_
  refine (congrArg _ h2).trans ?_
  refine (congrArg (fun z => (((k : ℤ) + 1).negOnePow : ℤ) • z)
    ((congrArg (· + _) h3).trans (zero_add _))).trans ?_
  refine ((Int.cast_smul_eq_zsmul ((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj (op U))
    _ _).symm.trans (smul_smul _ _ _)).trans (congrArg (· • g) ?_)
  rw [← mul_assoc, hε, one_mul]

end Leibniz

end SheafOfModules
