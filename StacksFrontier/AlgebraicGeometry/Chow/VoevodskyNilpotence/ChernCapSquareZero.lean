module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapDimensionInduction
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.TensorChernClasses

/-!
# `c₁(ℒ) ∩ c₁(ℒ) ∩ − = 0` for an invertible module on a curve

Let `X` be Noetherian, locally of finite type over the base of chapter 42, of topological
dimension at most one and carrying an ample invertible module, and let `ℒ` be an invertible
`𝒪_X`-module. For every test scheme `u : T ⟶ X` locally of finite type, of any dimension, the
two-fold first Chern class cap product `c₁(u^*ℒ) ∩ c₁(u^*ℒ) ∩ −` vanishes on all of `A_*(T)`: this
is Stacks 0FDX at `d = 1`, the case `d = 1` of
`Stacks.Chow.iteratedChernCapOnChow_ofFn_eq_zero_of_topologicalKrullDim_le`. Equivalently, the
shift operator `Stacks.Chow.firstChernShift` of `u^*ℒ` squares to zero in `AddMonoid.End` of the
graded product `Stacks.Chow.ChowGradedProduct` of the Chow groups of `T`.

## Main results

* `Stacks.Chow.firstChernCapStep_eq_invCap_capOnChow`: the degree-raising step
  `Stacks.Chow.firstChernCapStep` of an invertible module is the cap operation of
  `Stacks.Chow.invCap`, up to a transport of degree.
* `Stacks.Chow.iteratedChernCapOnChow_pair_eq`: the iterated cap product at a two-element list of
  one operator is that operator's cap twice.
* `Stacks.Chow.invCap_capOnChow_capOnChow_eq_zero_of_topologicalKrullDim_le_one`: Stacks 0FDX at
  `d = 1`, on every test scheme locally of finite type.
* `Stacks.Chow.firstChernShift_mul_self_eq_zero_of_topologicalKrullDim_le_one`: the shift operator
  of `u^*ℒ` squares to zero.

## References

* [Stacks Project, Tag 0FDX](https://stacks.math.columbia.edu/tag/0FDX)
* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Stacks.AlgebraicGeometry.AmpleLimit

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u})

/-! ### The two identifications -/

/-- **The degree-raising step of an invertible module is the cap operation of its cap operator.**
`Stacks.Chow.firstChernCapStep` of `M` at `x ∈ A_{n-i}` is the cap operation of
`Stacks.Chow.invCap` of `M` at `y`, the class `x` read in degree `(n - (i + 1)) + 1`. -/
theorem firstChernCapStep_eq_invCap_capOnChow {X : Scheme.{u}} (q : X ⟶ C.S)
    [LocallyOfFiniteType q] (n : ℤ) (M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    (hfac : InvertibleChernCapDescends C q M) (i : ℕ) (x : chowGroup C q (n - (i : ℤ)))
    (y : chowGroup C q (n - ((i + 1 : ℕ) : ℤ) + 1)) (hxy : x ≍ y) :
    firstChernCapStep C q n M hfac i x =
      (invCap C q M).capOnChow C q (n - ((i + 1 : ℕ) : ℤ)) y := by
  have key : ∀ (k : ℤ) (z : chowGroup C q (k + 1)),
      firstChernClassCapOnChow C q k (firstChernComponentCycleRule C q k M) (hfac k) z =
        (invCap C q M).capOnChow C q k z := by
    intro k z
    obtain ⟨α, rfl⟩ := QuotientAddGroup.mk'_surjective _ z
    rw [firstChernClassCapOnChow_mk, invCap_capOnChow_mk]
  simp only [firstChernCapStep]
  rw [chowGroupDegreeCast_apply, key]
  congr 1
  exact chowGroup_eq_of_heq C q ((chowGroupCast_heq C q _ x).trans hxy)

/-- **An iterated cap at a two-element list of one operator is that operator's cap twice.** The
class `z` is `w` read in the degree the two-fold cap iterates from. -/
theorem iteratedChernCapOnChow_pair_eq {X : Scheme.{u}} (q : X ⟶ C.S) [LocallyOfFiniteType q]
    (O : ChernCapOperator C q) (k : ℤ)
    (w : chowGroup C q (k + ((O :: [O] : List (ChernCapOperator C q)).length : ℤ)))
    (z : chowGroup C q (k + 1 + 1)) (hwz : w ≍ z) :
    iteratedChernCapOnChow C q (O :: [O]) k w =
      O.capOnChow C q k (O.capOnChow C q (k + 1) z) := by
  have hy : k + ((O :: [O] : List (ChernCapOperator C q)).length : ℤ) =
      k + 1 + (([O] : List (ChernCapOperator C q)).length : ℤ) := by
    simp only [List.length_cons]; push_cast; ring
  rw [iteratedChernCapOnChow_cons_eq C q O [O] k w (chowGroupCast C q hy w)
      (chowGroupCast_heq C q hy w).symm,
    iteratedChernCapOnChow_singleton_eq C q O (k + 1) (chowGroupCast C q hy w) z
      ((chowGroupCast_heq C q hy w).trans hwz)]

/-! ### Stacks 0FDX at `d = 1` -/

/-- **Stacks 0FDX at `d = 1`, on every test scheme locally of finite type.** For `X` locally of
finite type over the base of chapter 42, Noetherian, carrying an ample invertible module and of
topological dimension at most one — a curve — and for an invertible `𝒪_X`-module `ℒ`,

  `c₁(u^*ℒ) ∩ c₁(u^*ℒ) ∩ z = 0`

for every Chow class `z` of every test scheme `u : T ⟶ X` locally of finite type. No bound is
placed on the dimension of `T`. -/
theorem invCap_capOnChow_capOnChow_eq_zero_of_topologicalKrullDim_le_one {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [IsNoetherian X] (A : X.Modules)
    [Stacks.Ample.IsInvertibleModule X A] (hA : Stacks.Ample.IsAmple X A)
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    {T : Scheme.{u}} (u : T ⟶ X) [LocallyOfFiniteType u] (q : T ⟶ C.S) [LocallyOfFiniteType q]
    (hq : u ≫ sX = q) (k : ℤ) (z : chowGroup C q (k + 1 + 1)) :
    (invCap C q ((Scheme.Modules.pullback u).obj L)).capOnChow C q k
      ((invCap C q ((Scheme.Modules.pullback u).obj L)).capOnChow C q (k + 1) z) = 0 := by
  have hd : k + 1 + 1 = k + ((List.ofFn fun _ : Fin 2 =>
      invCap C q ((Scheme.Modules.pullback u).obj L)).length : ℤ) := by
    simp only [List.length_ofFn]; push_cast; ring
  have hmain := iteratedChernCapOnChow_ofFn_eq_zero_of_topologicalKrullDim_le C 1 sX A hA
    (by exact_mod_cast hdim) (fun _ : Fin 2 => L) u q hq k (chowGroupCast C q hd z)
  exact (iteratedChernCapOnChow_pair_eq C q (invCap C q ((Scheme.Modules.pullback u).obj L)) k
    (chowGroupCast C q hd z) z (chowGroupCast_heq C q hd z)).symm.trans hmain

/-- **The shift operator of a pullback from a curve squares to zero.** For `ℒ` invertible on a
Noetherian `X` of topological dimension at most one carrying an ample invertible module, and a
test scheme `u : T ⟶ X` locally of finite type, the shift operator of `u^*ℒ` squares to zero in
`AddMonoid.End` of the graded product of the Chow groups of `T`. -/
theorem firstChernShift_mul_self_eq_zero_of_topologicalKrullDim_le_one {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [IsNoetherian X] (A : X.Modules)
    [Stacks.Ample.IsInvertibleModule X A] (hA : Stacks.Ample.IsAmple X A)
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    {T : Scheme.{u}} (u : T ⟶ X) [LocallyOfFiniteType u] (q : T ⟶ C.S) [LocallyOfFiniteType q]
    (hq : u ≫ sX = q) (n : ℤ)
    (hfac : InvertibleChernCapDescends C q ((Scheme.Modules.pullback u).obj L)) :
    firstChernShift C q n ((Scheme.Modules.pullback u).obj L) hfac *
      firstChernShift C q n ((Scheme.Modules.pullback u).obj L) hfac = 0 := by
  have hstep : ∀ (j : ℕ) (x : chowGroup C q (n - (j : ℤ))),
      firstChernCapStep C q n ((Scheme.Modules.pullback u).obj L) hfac (j + 1)
        (firstChernCapStep C q n ((Scheme.Modules.pullback u).obj L) hfac j x) = 0 := by
    intro j x
    have hcap : ∀ (i : ℕ) (y : chowGroup C q (n - (i : ℤ))),
        firstChernCapStep C q n ((Scheme.Modules.pullback u).obj L) hfac i y =
          (invCap C q ((Scheme.Modules.pullback u).obj L)).capOnChow C q (n - ((i + 1 : ℕ) : ℤ))
            (chowGroupCast C q (by push_cast; ring) y) := fun i y =>
      firstChernCapStep_eq_invCap_capOnChow C q n _ hfac i y _ (chowGroupCast_heq C q _ y).symm
    rw [hcap (j + 1), hcap j]
    refine Eq.trans ?_ (invCap_capOnChow_capOnChow_eq_zero_of_topologicalKrullDim_le_one C sX A hA
      hdim L u q hq (n - ((j + 1 + 1 : ℕ) : ℤ))
      (chowGroupCast C q (by push_cast; ring) x))
    congr 1
    refine chowGroup_eq_of_heq C q ((chowGroupCast_heq C q _ _).trans ?_)
    exact capOnChow_heq C q _ (by push_cast; ring)
      ((chowGroupCast_heq C q _ x).trans (chowGroupCast_heq C q _ x).symm)
  ext h' i
  match i with
  | 0 => rfl
  | 1 => simp
  | (j + 2) => exact hstep j (h' j)

end Stacks.Chow

end
