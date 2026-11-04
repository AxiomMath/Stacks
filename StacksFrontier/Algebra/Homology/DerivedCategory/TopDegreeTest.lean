module

public import StacksFrontier.Algebra.Homology.DerivedCategory.TopTruncationExt

/-!
# Morphisms out of an object of cohomological dimension zero are seen in degree zero

Let `X` be an object of an abelian category `𝒜` with `Ext^i(X, -) = 0` for every `i ≥ 1` (for
instance the constant sheaf on the spectrum of a separably closed field). Then:

* `Hom(X[0], L) = 0` for every bounded below `L` living in degrees `≤ -1`
  (`Stacks.TopTruncationExt.eq_zero_of_isLE_neg_one`), by induction on the length of `L`
  through its truncation triangles;
* a morphism `w : X[0] ⟶ K[n]` with `K` bounded below and living in degrees `≤ n` is zero as soon
  as `H⁰(w) = 0` (`Stacks.TopTruncationExt.eq_zero_of_homologyFunctor_map_eq_zero`): it then
  factors through the truncation `τ_{< 0}(K[n])`, which lives in degrees `≤ -1`.

The second statement is the corner of the Leray spectral sequence of a curve over a separably
closed field: a class of `H^n_c` of the curve vanishes once its image in `H⁰` of the top direct
image does. It is used for the class of a point of the fibre curve of an elementary fibration, in
the proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

Also: every morphism `X[0] ⟶ Y[0][m]` of `D⁺(𝒜)` is the reading `Stacks.TopTruncationExt.extPlus`
of a class of `Ext^m(X, Y)` (`Stacks.TopTruncationExt.extPlus_surjective`).

## Main results

* `Stacks.TopTruncationExt.eq_zero_of_isLE_neg_one`.
* `Stacks.TopTruncationExt.eq_zero_of_homologyFunctor_map_eq_zero`.
* `Stacks.TopTruncationExt.extPlus_surjective`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian CategoryTheory.Pretriangulated

namespace Stacks.TopTruncationExt

universe w

/-- The truncation triangle `τ_{< s} L ⟶ L ⟶ τ_{≥ s} L` of `L ∈ [l, u]` has its third vertex in
`[q, u]` and its first vertex in `[l', p]`, for any `q ≤ s`, `p ≥ s - 1`, `l' ≤ l` and `l' ≤ s + 1`
(and `s ≤ u + 2`). -/
private theorem triangleLTGE_bounds {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] (L : DerivedCategory A) (s l l' u p q : ℤ) [L.IsGE l]
    [L.IsLE u] (hq : q ≤ s) (hp : s - 1 ≤ p) (hl : l' ≤ l) (hl' : l' ≤ s + 1) (hu : s ≤ u + 2) :
    let T := (DerivedCategory.TStructure.t (C := A)).triangleLTGE s |>.obj L
    (T.obj₃ : DerivedCategory A).IsGE q ∧ (T.obj₃ : DerivedCategory A).IsLE u ∧
      (T.obj₁ : DerivedCategory A).IsLE p ∧ (T.obj₁ : DerivedCategory A).IsGE l' := by
  intro T
  let t := DerivedCategory.TStructure.t (C := A)
  have hT := t.triangleLTGE_distinguished s L
  have h₃ge : t.IsGE T.obj₃ s := by
    change t.IsGE ((t.truncGE s).obj L) s
    infer_instance
  have h₁le : t.IsLE T.obj₁ (s - 1) := t.isLE_truncLT_obj L s (s - 1) (by omega)
  refine ⟨t.isGE_of_ge _ _ s hq, ?_, t.isLE_of_le _ _ _ hp, ?_⟩
  · have h₂ : t.IsLE (T.obj₁⟦(1 : ℤ)⟧) u := by
      have : t.IsLE (T.obj₁⟦(1 : ℤ)⟧) (s - 2) := t.isLE_shift T.obj₁ (s - 1) 1 (s - 2) (by omega)
      exact t.isLE_of_le _ (s - 2) u (by omega)
    exact t.isLE₂ T.rotate (rot_of_distTriang _ hT) u ‹L.IsLE u› h₂
  · have h₃ : t.IsGE (T.obj₃⟦(-1 : ℤ)⟧) l' := by
      have : t.IsGE (T.obj₃⟦(-1 : ℤ)⟧) (s + 1) := t.isGE_shift T.obj₃ s (-1) (s + 1) (by omega)
      exact t.isGE_of_ge _ _ (s + 1) hl'
    exact t.isGE₂ T.invRotate (inv_rot_of_distTriang _ hT) l' h₃ (t.isGE_of_ge L _ l hl)

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A] [HasExt.{w} A]

/-- **Every morphism `X[0] ⟶ Y[0][m]` of `D⁺(𝒜)` is the reading of a class of `Ext^m(X, Y)`.** -/
theorem extPlus_surjective (X Y : A) (m : ℕ) :
    Function.Surjective (extPlus : Ext.{w} X Y m → _) := by
  intro φ
  refine ⟨Ext.homEquiv.symm (DerivedCategory.Plus.ι.map φ ≫
    (DerivedCategory.Plus.ι.commShiftIso (m : ℤ)).hom.app _), ?_⟩
  apply DerivedCategory.Plus.ι.map_injective
  simp only [extPlus, Functor.map_preimage, Ext.hom, Equiv.apply_symm_apply]
  exact (Category.assoc _ _ _).trans ((congrArg _ (Iso.hom_inv_id_app _ _)).trans
    (Category.comp_id _))

section Vanishing

variable (X : A) (hX : ∀ (i : ℕ) (M : A), 1 ≤ i → Subsingleton (Ext.{w} X M i))

include hX in
/-- A morphism `X[0] ⟶ L` vanishes when `L` lives in the single degree `-d`, `d ≥ 1`. -/
theorem eq_zero_of_isGE_of_isLE (d : ℕ) (hd : 1 ≤ d) (L : DerivedCategory A)
    [L.IsGE (-(d : ℤ))] [L.IsLE (-(d : ℤ))]
    (f : (DerivedCategory.singleFunctor A 0).obj X ⟶ L) : f = 0 := by
  obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE L (-(d : ℤ))
  let e' : L ≅ ((DerivedCategory.singleFunctor A 0).obj M)⟦(d : ℤ)⟧ :=
    e ≪≫ (((DerivedCategory.singleFunctors A).shiftIso (d : ℤ) (-(d : ℤ)) 0 (by omega)).app M).symm
  have := hX d M hd
  have h0 : (f ≫ e'.hom : ShiftedHom _ _ (d : ℤ)) = 0 := by
    simpa only [Ext.hom, Equiv.apply_symm_apply, Ext.zero_hom] using
      congrArg (fun z : Ext.{w} X M d => z.hom)
        (Subsingleton.elim (Ext.homEquiv.symm (f ≫ e'.hom : ShiftedHom _ _ (d : ℤ)))
          (0 : Ext.{w} X M d))
  exact (cancel_mono e'.hom).1 (h0.trans zero_comp.symm)

include hX in
/-- **`Hom(X[0], L) = 0` for `L` bounded below and living in degrees `≤ -1`.** -/
theorem eq_zero_of_isLE_neg_one (n : ℕ) (L : DerivedCategory A) [L.IsGE (-1 - (n : ℤ))]
    [L.IsLE (-1)] (f : (DerivedCategory.singleFunctor A 0).obj X ⟶ L) : f = 0 := by
  induction n generalizing L with
  | zero =>
    have : L.IsGE (-((1 : ℕ) : ℤ)) := DerivedCategory.TStructure.t.isGE_of_ge L _ (-1 - 0)
      (by omega)
    have : L.IsLE (-((1 : ℕ) : ℤ)) := by simpa using ‹L.IsLE (-1)›
    exact eq_zero_of_isGE_of_isLE X hX 1 le_rfl L f
  | succ n ih =>
    let t := DerivedCategory.TStructure.t (C := A)
    let a : ℤ := -1 - ((n + 1 : ℕ) : ℤ)
    let T := (t.triangleLTGE (a + 1)).obj L
    have hT := t.triangleLTGE_distinguished (a + 1) L
    obtain ⟨h₃ge, h₃le, h₁le, h₁ge⟩ := triangleLTGE_bounds L (a + 1) (-1 - ((n + 1 : ℕ) : ℤ)) a
      (-1) a (-1 - (n : ℤ)) (by omega) (by omega) (by omega) (by omega) (by omega)
    obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ T hT f (ih T.obj₃ _)
    have hd : -((n + 2 : ℕ) : ℤ) = a := by push_cast; omega
    have : t.IsGE T.obj₁ (-((n + 2 : ℕ) : ℤ)) := by rwa [hd]
    have : t.IsLE T.obj₁ (-((n + 2 : ℕ) : ℤ)) := by rwa [hd]
    rw [hg, eq_zero_of_isGE_of_isLE X hX (n + 2) (by omega) T.obj₁ g]
    exact zero_comp

include hX in
/-- **A morphism `X[0] ⟶ K[n]` is seen by `H⁰`** when `K` is bounded below and lives in
degrees `≤ n`: if `H⁰(w) = 0`, then `w = 0`. -/
theorem eq_zero_of_homologyFunctor_map_eq_zero (n : ℤ) (K : DerivedCategory A) (b : ℕ)
    [K.IsLE n] [K.IsGE (n - b)]
    (w : (DerivedCategory.singleFunctor A 0).obj X ⟶ K⟦n⟧)
    (hw : (DerivedCategory.homologyFunctor A 0).map w = 0) : w = 0 := by
  let t := DerivedCategory.TStructure.t (C := A)
  let T := (t.triangleLTGE 0).obj (K⟦n⟧)
  have hT := t.triangleLTGE_distinguished 0 (K⟦n⟧)
  have hKle : t.IsLE (K⟦n⟧) 0 := t.isLE_shift K n n 0 (by omega)
  have hKge : t.IsGE (K⟦n⟧) (-(b : ℤ)) := t.isGE_shift K (n - b) n (-(b : ℤ)) (by omega)
  obtain ⟨h₃ge, h₃le, h₁le, h₁ge⟩ := triangleLTGE_bounds (K⟦n⟧) 0 (-(b : ℤ)) (-1 - (b : ℤ)) 0
    (-1) 0 (by omega) (by omega) (by omega) (by omega) (by omega)
  have : ((DerivedCategory.singleFunctor A 0).obj X).IsLE 0 := inferInstance
  have h2 : w ≫ T.mor₂ = 0 := by
    apply (DerivedCategory.bijective_homologyFunctor_map_of_isLE_of_isGE _ T.obj₃ 0).1
    show (DerivedCategory.homologyFunctor A 0).map (w ≫ T.mor₂) =
      (DerivedCategory.homologyFunctor A 0).map 0
    have hc : (DerivedCategory.homologyFunctor A 0).map (w ≫ T.mor₂) =
        (DerivedCategory.homologyFunctor A 0).map w ≫
          (DerivedCategory.homologyFunctor A 0).map T.mor₂ :=
      Functor.map_comp _ _ _
    rw [hc, hw, zero_comp, Functor.map_zero]
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ T hT w h2
  rw [hg, eq_zero_of_isLE_neg_one X hX b T.obj₁ g]
  exact zero_comp

end Vanishing

end Stacks.TopTruncationExt

end
