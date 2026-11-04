module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.WayOutPairing

/-!
# Transporting a Yoneda duality along identifications of `Ext` groups, with a shift

Let `t : Ext^N(O, D) → A` and `t' : Ext^{N'}(O', D') → A` be traces, possibly in two different
abelian categories, with `N = N' + c`. Suppose `Ext^i(O, F) ≅ Ext^i(O', F')` and
`Ext^j(F', D') ≅ Ext^{j+c}(F, D)` compatibly with the two pairings, and that the degrees outside
the common range vanish: `Ext^i(O, F) = 0` for `i > N'` and `Ext^j(F, D) = 0` for `j < c`. Then
duality holds at `F` for `t` if and only if it holds at `F'` for `t'`.

This is how cohomological purity enters Poincaré duality: for a smooth closed `i : T → X` of
codimension `c`, `Ext^{j+2c}_X(i_* G, Λ_X) ≅ Ext^j_T(G, Λ_T)`, while `Ext^i(Λ, i_* G)` is the
cohomology of `T`; so duality on `X` at `i_* G` (in dimension `N = 2 dim X`) is duality on `T`
at `G` (in dimension `N' = 2 dim T`).

## Main results

* `CategoryTheory.Abelian.Ext.isDualityPerfect_iff_of_addEquiv`.
-/

@[expose] public section

universe w w' v v' u u'

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {C' : Type u'} [Category.{v'} C'] [Abelian C'] [HasExt.{w'} C']
  {A : Type*} [AddCommGroup A]

/-- **Duality is invariant under compatible identifications of the `Ext` groups, with a shift
`c` on the dualizing side.** -/
theorem isDualityPerfect_iff_of_addEquiv {O D F : C} {N : ℕ} (t : Ext.{w} O D N →+ A)
    {O' D' F' : C'} {N' : ℕ} (t' : Ext.{w'} O' D' N' →+ A) (c : ℕ) (hN : N = N' + c)
    (α : ∀ i, Ext.{w} O F i ≃+ Ext.{w'} O' F' i)
    (β : ∀ j, Ext.{w'} F' D' j ≃+ Ext.{w} F D (j + c))
    (hcomp : ∀ (i j : ℕ) (h : i + j = N') (x : Ext.{w} O F i) (y : Ext.{w'} F' D' j),
      t' ((α i x).comp y h) = t (x.comp (β j y) (by omega)))
    (hO : ∀ i, N' < i → Subsingleton (Ext.{w} O F i))
    (hD : ∀ j, j < c → Subsingleton (Ext.{w} F D j)) :
    IsDualityPerfect O D N t F ↔ IsDualityPerfect O' D' N' t' F' := by
  have key : ∀ (i j : ℕ) (h : i + j = N'), Function.Bijective
      (dualityPairing O D N t F (show i + (j + c) = N by omega)) ↔
      Function.Bijective (dualityPairing O' D' N' t' F' h) := by
    intro i j h
    have h' : i + (j + c) = N := by omega
    let pre : (Ext.{w} F D (j + c) →+ A) ≃ (Ext.{w'} F' D' j →+ A) :=
      { toFun φ := φ.comp (β j).toAddMonoidHom
        invFun φ := φ.comp (β j).symm.toAddMonoidHom
        left_inv φ := by ext; simp
        right_inv φ := by ext; simp }
    have hcomm : pre ∘ dualityPairing O D N t F h' =
        dualityPairing O' D' N' t' F' h ∘ α i := by
      funext x
      ext y
      exact (hcomp i j h x y).symm
    rw [← Function.Bijective.of_comp_iff' pre.bijective (dualityPairing O D N t F h'), hcomm]
    exact Function.Bijective.of_comp_iff _ (α i).bijective
  refine ⟨fun hF i j h => (key i j h).1 (hF i (j + c) (by omega)), fun hF' i j h => ?_⟩
  by_cases hi : i ≤ N'
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + c := ⟨j - c, by omega⟩
    exact (key i j' (by omega)).2 (hF' i j' (by omega))
  · have := hO i (by omega)
    have := hD j (by omega)
    refine ⟨fun x x' _ => Subsingleton.elim x x', fun φ => ⟨0, ?_⟩⟩
    ext y
    rw [Subsingleton.elim y 0, map_zero, map_zero]

end CategoryTheory.Abelian.Ext
