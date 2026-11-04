module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ApproximationTriangle

/-!
# `Ext` against a morphism whose cone lives in low degrees

Let `𝒜` be an abelian category and let `P ⟶ E ⟶ Q ⟶ P[1]` be a distinguished triangle of `D(𝒜)`
whose third term `Q` has no cohomology above degree `r`.  For an object `M` with no cohomology
below degree `a`, precomposition with `P ⟶ E` is bijective

`Ext^i(E, M) ⟶ Ext^i(P, M)`

as soon as `i + r + 2 ≤ a`: the two neighbouring groups `Hom(Q, M[i])` and `Hom(Q[-1], M[i])` of
the long exact sequence vanish by Stacks 06XS.  This is the argument of the proof of Stacks 08JR
comparing `E` with a perfect approximation `P`.

Conversely, a bounded above object `D` whose cohomology objects lie in a class `Pc`, and against
which every `Ext^i(D, F)` with `F ∈ Pc` and `i ≤ N` vanishes, has no cohomology in degrees `≥ -N`:
otherwise its top cohomology `H^t(D) ∈ Pc` gives the nonzero class `D ⟶ H^t(D)[-t]`, with
`-t ≤ N`.  Applied to the cone of a morphism `f : A ⟶ A'`, a morphism inducing bijections on
`Ext^i(-, F)` for `i ≤ N` is an isomorphism on cohomology in degrees `> -N`.  This is the hint
"take the cone of `L_n ⟶ L_{n+1}` and look at its last nonvanishing cohomology sheaf" of the
proof of Stacks 08JR.

## Main results

* `DerivedCategory.bijective_comp_shiftedHom_of_isLE_of_isGE`: the comparison of `Ext` groups.
* `DerivedCategory.bijective_comp_shiftedHom_of_isIso_homologyFunctor_map`: the same for a
  morphism which is an isomorphism on cohomology above a degree.
* `DerivedCategory.isLE_of_forall_eq_zero_of_isLE`: the detection of the top cohomology.
* `DerivedCategory.isIso_homologyFunctor_map_of_bijective_comp_shiftedHom`: a morphism which is
  bijective on `Ext^i(-, F)` for `i ≤ N` is an isomorphism on `H^j` for `j > -N`.

## Implementation notes

The model of the derived category is arbitrary.  `Ext^i(E, M)` is `E ⟶ M⟦i⟧`
(`CategoryTheory.DerivedCategory.Ext`).

## References

* [Stacks Project, Tag 08JR](https://stacks.math.columbia.edu/tag/08JR)
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- **Precomposition with `α : P ⟶ E` is bijective on `Ext^i(-, M)` when the cone of `α` is
`≤ r`, `M` is `≥ a` and `i + r + 2 ≤ a`.**  Both `Hom(Q, M[i])` and `Hom(Q[-1], M[i])` vanish, the
cone `Q` and its shift `Q[-1]` lying strictly below `M[i]` for the canonical t-structure. -/
theorem bijective_comp_shiftedHom_of_isLE_of_isGE {P E Q : DerivedCategory C} (α : P ⟶ E)
    (β : E ⟶ Q) (γ : Q ⟶ P⟦(1 : ℤ)⟧) (hT : Triangle.mk α β γ ∈ distTriang (DerivedCategory C))
    (r : ℤ) [Q.IsLE r] (M : DerivedCategory C) (a : ℤ) [M.IsGE a] (i : ℤ) (hi : i + r + 2 ≤ a) :
    Function.Bijective (fun e : E ⟶ M⟦i⟧ => α ≫ e) := by
  have hMi : (M⟦i⟧).IsGE (a - i) := TStructure.t.isGE_shift M a i (a - i) (by omega)
  have hQ' : (Q⟦(-1 : ℤ)⟧).IsLE (r + 1) := TStructure.t.isLE_shift Q r (-1) (r + 1) (by omega)
  refine ⟨fun e₁ e₂ h => ?_, fun g => ?_⟩
  · have h0 : α ≫ (e₁ - e₂) = 0 := by
      simp only [Preadditive.comp_sub]
      exact sub_eq_zero.2 h
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ _ hT (e₁ - e₂) h0
    have : g = 0 :=
      TStructure.t.zero_of_isLE_of_isGE (X := Q) g r (a - i) (by omega) inferInstance hMi
    rw [this, comp_zero] at hg
    exact sub_eq_zero.1 hg
  · have hT' := inv_rot_of_distTriang _ hT
    obtain ⟨e, he⟩ := Triangle.yoneda_exact₂ _ hT' g
      (TStructure.t.zero_of_isLE_of_isGE _ (r + 1) (a - i) (by omega) hQ' hMi)
    exact ⟨e, he.symm⟩

/-- **Precomposition with a morphism which is an isomorphism on cohomology above `s` is bijective
on `Ext^i(-, M)` for `M ≥ a` and `i + s + 2 ≤ a`**: the cone of the morphism lives in degrees
`≤ s`. -/
theorem bijective_comp_shiftedHom_of_isIso_homologyFunctor_map {P E : DerivedCategory C}
    (c : P ⟶ E) (s : ℤ) (hc : ∀ j : ℤ, s < j → IsIso ((homologyFunctor C j).map c))
    (M : DerivedCategory C) (a : ℤ) [M.IsGE a] (i : ℤ) (hi : i + s + 2 ≤ a) :
    Function.Bijective (fun e : E ⟶ M⟦i⟧ => c ≫ e) := by
  obtain ⟨Q, β, γ, hT⟩ := distinguished_cocone_triangle c
  have : Q.IsLE s := by
    rw [DerivedCategory.isLE_iff]
    intro j hj
    exact CategoryTheory.isZero_homology_obj₃_of_distinguished (s + 1) _ hT
      (fun k hk => hc k (by omega)) (hc (s + 1) (by omega)).epi_of_iso j (by omega)
  exact bijective_comp_shiftedHom_of_isLE_of_isGE c β γ hT s M a i hi

/-- **The top cohomology detects `Ext` out of a bounded above object.**  Let `D` be bounded above,
let `Pc` be a class of objects of `𝒜` containing every cohomology object of `D`, and suppose every
morphism `D ⟶ F[i]` vanishes for `F ∈ Pc` and `i ≤ N`.  Then `D` has no cohomology in degrees
`≥ -N`.  If `t ≥ -N` were the largest degree with `H^t(D) ≠ 0`, then `D ≤ t`, and by Stacks 06XS
the classes `D ⟶ H^t(D)[0][-t]` would correspond to the endomorphisms of `H^t(D)`. -/
theorem isLE_of_forall_eq_zero_of_isLE (D : DerivedCategory C) (t₀ : ℤ) [D.IsLE t₀] (N : ℤ)
    (Pc : C → Prop) (hPc : ∀ j : ℤ, Pc ((homologyFunctor C j).obj D))
    (hvan : ∀ F : C, Pc F → ∀ i : ℤ, i ≤ N →
      ∀ g : D ⟶ ((singleFunctor C 0).obj F)⟦i⟧, g = 0) :
    D.IsLE (-N - 1) := by
  -- Every cohomology object in the window `[-N, t₀]` vanishes, by descending induction.
  have key : ∀ k : ℕ, ∀ t : ℤ, t = t₀ - k → -N ≤ t → D.IsLE t →
      IsZero ((homologyFunctor C t).obj D) := by
    intro k t _ ht hDt
    let A := (homologyFunctor C t).obj D
    have hbij := bijective_homologyFunctor_shiftMap_of_isLE_of_isGE D
      ((singleFunctor C 0).obj A) t 0 (-t) 0 (by omega) le_rfl
    have hsub : Subsingleton ((homologyFunctor C t).obj D ⟶
        (homologyFunctor C 0).obj ((singleFunctor C 0).obj A)) := by
      refine ⟨fun x y => ?_⟩
      obtain ⟨gx, rfl⟩ := hbij.2 x
      obtain ⟨gy, rfl⟩ := hbij.2 y
      rw [hvan A (hPc t) (-t) (by omega) gx, hvan A (hPc t) (-t) (by omega) gy]
    let e : (homologyFunctor C 0).obj ((singleFunctor C 0).obj A) ≅ A :=
      (singleFunctorCompHomologyFunctorIso C 0).app A
    rw [IsZero.iff_id_eq_zero, ← e.inv_hom_id, hsub.allEq e.inv 0, zero_comp]
  -- Assemble.
  have step : ∀ k : ℕ, D.IsLE (max (t₀ - k) (-N - 1)) := by
    intro k
    induction k with
    | zero =>
      exact TStructure.t.isLE_of_le D t₀ _ (by simp)
    | succ k ih =>
      by_cases hk : t₀ - k ≤ -N - 1
      · rw [max_eq_right hk] at ih
        exact TStructure.t.isLE_of_le D (-N - 1) _ (le_max_right _ _)
      · rw [max_eq_left (by omega)] at ih
        have hz := key k (t₀ - k) rfl (by omega) ih
        rw [DerivedCategory.isLE_iff] at ih ⊢
        intro i hi
        by_cases hit : i = t₀ - k
        · subst hit
          exact hz
        · exact ih i (by push_cast at hi ⊢; omega)
  have hk := step (t₀ + N + 1).toNat
  exact TStructure.t.isLE_of_le D (max (t₀ - ((t₀ + N + 1).toNat : ℕ)) (-N - 1)) (-N - 1)
    (by omega)

/-- **A morphism which is bijective on `Ext^i(-, F)` for `i ≤ N` and every `F ∈ Pc` is an
isomorphism on `H^j` for `j > -N`**, provided its cone `D` is bounded above with cohomology in
`Pc`.  The long exact sequence makes every `Ext^i(D, F)`, `i ≤ N`, vanish, so `D ≤ -N - 1` by
`DerivedCategory.isLE_of_forall_eq_zero_of_isLE`. -/
theorem isIso_homologyFunctor_map_of_bijective_comp_shiftedHom {A A' D : DerivedCategory C}
    (f : A ⟶ A') (g : A' ⟶ D) (h : D ⟶ A⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang (DerivedCategory C)) (t₀ : ℤ) [D.IsLE t₀] (N : ℤ)
    (Pc : C → Prop) (hPc : ∀ j : ℤ, Pc ((homologyFunctor C j).obj D))
    (hbij : ∀ F : C, Pc F → ∀ i : ℤ, i ≤ N →
      Function.Bijective (fun e : A' ⟶ ((singleFunctor C 0).obj F)⟦i⟧ => f ≫ e))
    (j : ℤ) (hj : -N < j) :
    IsIso ((homologyFunctor C j).map f) := by
  have hD : D.IsLE (-N - 1) := by
    refine isLE_of_forall_eq_zero_of_isLE D t₀ N Pc hPc fun F hF i hi u => ?_
    let M := (singleFunctor C 0).obj F
    -- `g ≫ u = 0` by injectivity in degree `i`.
    have hgu : g ≫ u = 0 :=
      (hbij F hF i hi).1 (by
        have hfg : f ≫ g = 0 := comp_distTriang_mor_zero₁₂ _ hT
        show f ≫ g ≫ u = f ≫ 0
        rw [← Category.assoc, hfg, zero_comp, comp_zero])
    obtain ⟨v, hv⟩ := Triangle.yoneda_exact₃ _ hT u hgu
    -- `v : A⟦1⟧ ⟶ M⟦i⟧` is the shift of a class `A ⟶ M⟦i - 1⟧`, which factors through `f`.
    let ε := (shiftFunctorAdd' (DerivedCategory C) (i - 1) 1 i (by omega)).app M
    let w' : A ⟶ M⟦i - 1⟧ := (shiftFunctor (DerivedCategory C) (1 : ℤ)).preimage (v ≫ ε.hom)
    obtain ⟨w, hw⟩ := (hbij F hF (i - 1) (by omega)).2 w'
    have hv' : v = (f ≫ w)⟦(1 : ℤ)⟧' ≫ ε.inv := by
      have : (f ≫ w)⟦(1 : ℤ)⟧' = v ≫ ε.hom := by
        have hw' : f ≫ w = w' := hw
        show (shiftFunctor (DerivedCategory C) (1 : ℤ)).map (f ≫ w) = _
        rw [hw', Functor.map_preimage]
      rw [this, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have h3 : h ≫ f⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ hT
    rw [hv, hv']
    simp only [Triangle.mk_mor₃, Functor.map_comp, ← Category.assoc, h3, zero_comp]
  have hz : ∀ k : ℤ, -N ≤ k → IsZero ((homologyFunctor C k).obj D) := fun k hk =>
    (DerivedCategory.isLE_iff D (-N - 1)).1 hD k (by omega)
  let F := homologyFunctor C 0
  have hepi : Epi ((homologyFunctor C j).map f) :=
    (F.homologySequence_exact₂ _ hT j).epi_f ((hz j (by omega)).eq_of_tgt _ _)
  have hmono : Mono ((homologyFunctor C j).map f) :=
    (F.homologySequence_exact₁ _ hT (j - 1) j (by omega)).mono_g
      ((hz (j - 1) (by omega)).eq_of_src _ _)
  exact isIso_of_mono_of_epi _

end DerivedCategory

end
