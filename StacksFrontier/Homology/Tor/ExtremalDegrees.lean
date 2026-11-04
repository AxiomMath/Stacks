module

public import StacksFrontier.Homology.DerivedComplete.TorsionAmplitude

/-!
# Extremal cohomological degrees under an exact functor

Let `F : D(C) → D(D)` be an exact functor of derived categories and let `X` be a bounded object
of `D(C)`.  This file reads the extremal nonvanishing cohomological degrees of `F(X)` off those
of `X` and the behaviour of `F` on the single complexes of the cohomology modules of `X`.

Two halves, both proved by the canonical truncation triangles:

* **the bounds.** If `F` carries each `H^i(X)[0]` into `D^{≥ b - i}`, respectively
  `D^{≤ b - i}`, then `F(X)` lies in `D^{≥ b}`, respectively `D^{≤ b}`.  This is an induction
  on the width of the cohomological window of `X`, and for the `≤` half it is the argument of
  `StacksDraft.PowerTorsionVanishing`, which has it as a private lemma for a bounded object; both
  halves are given here, publicly and with the two bounds of `X` as explicit arguments.

* **the nonvanishing**, which the bounds alone never give.  At the bottom: if `X` has no
  cohomology below `a` and `F(τ^{≥ a+1}X)` has none below `n + 1`, then
  `H^n(F(H^a(X)[-a])) ⟶ H^n(F(X))` is injective, because the connecting map into it comes from
  `H^{n-1}(F(τ^{≥ a+1}X)) = 0`.  Dually at the top with a surjection.  So nonvanishing of the
  cohomology of `F` at the extremal single complex of `X` propagates to `F(X)` itself.

## Main results

* `StacksDraft.ExtremalDegrees.isGE_map_of_homology`,
  `StacksDraft.ExtremalDegrees.isLE_map_of_homology` — the two bounds.
* `StacksDraft.ExtremalDegrees.not_isZero_homology_map_of_isGE` — the nonvanishing at the bottom.
* `StacksDraft.ExtremalDegrees.not_isZero_homology_map_of_isLE` — the nonvanishing at the top.
* `StacksDraft.ExtremalDegrees.extremalDegrees` — **the extremal degrees add.** For `X` with
  cohomology in `[a, b]` and `F` carrying each `H^i(X)[0]` into `D^{[c, d]}` with nonvanishing
  `c`-th cohomology at `H^a(X)[0]` and nonvanishing `d`-th cohomology at `H^b(X)[0]`, the
  cohomology of `F(X)` lies in `[a + c, b + d]` and does not vanish at either end.  So the
  bottom and top nonvanishing degrees of `F(X)` are those of `X` shifted by those of `F` on the
  cohomology modules of `X`.
* `StacksDraft.ExtremalDegrees.nonempty_iso_truncLT_succ_singleFunctor`,
  `StacksDraft.ExtremalDegrees.nonempty_iso_truncGE_singleFunctor` — the extremal truncations of
  a one-sidedly bounded object are the single complexes of its extremal cohomology.
* `StacksDraft.ExtremalDegrees.extremalDegrees_eq_zero_of_iso` — **the conclusion read back off a
  fixed object.** If `F(X) ≅ X` then the two shifts `c` and `d` are forced to be zero, so `F`
  carries each `H^i(X)[0]` to an object concentrated in degree zero. This is how the preceding
  theorem is consumed.
* `StacksDraft.ExtremalDegrees.eq_zero_of_isLE_of_iso` — its **top half alone**, which uses no
  lower bound and no nonvanishing at a bottom degree, and so is the reader for the one-sided
  computation of `StacksFrontier.Homology.Tor.ExtremalDegreesTop`.

## The extremal-degree Künneth step of [stacks 0E2D]

`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessDuality` needs this for `F = X ⊗ᴸ_A -` and
`T` an object of `D(A)` whose cohomology is killed by the maximal ideal.  The hypotheses of
`extremalDegrees` are then exactly the statement that `X ⊗ᴸ_A N[0]` has the same cohomological
window and the same extremal nonvanishing as `X ⊗ᴸ_A κ` for every `A`-module `N ≠ 0` killed by
the maximal ideal, **and that is now a theorem too**: it is the dévissage of a `κ`-vector space,
`StacksDraft.ResidueDevissage.of_residueField` of
`StacksFrontier.Homology.Tor.ResidueDevissage`, which also assembles the two into
`StacksDraft.ResidueDevissage.extremalDegrees_of_isTorsionBySet` — this theorem with all four of
its hypotheses discharged from the behaviour of `F` at the residue field alone.  Nothing of that
step is carried any longer.

## Implementation notes

The truncation comparison isomorphisms `τ^{<c}X ⟶ X` in degrees `< c` and `X ⟶ τ^{≥c}X` in
degrees `≥ c` are reproved here rather than imported: `StacksDraft.PowerTorsionVanishing` has
them as private lemmas.  They are read off the long exact sequence of the triangle
`τ^{<c}X ⟶ X ⟶ τ^{≥c}X` through
`CategoryTheory.DerivedCategory.HomologySequence`, which is also what the nonvanishing half uses.

The shift bookkeeping is confined to `StacksDraft.ExtremalDegrees.mapSingleShiftIso`: the single
complex in degree `a` is the shift by `-a` of the single complex in degree `0`, by the shift
isomorphism of the single functors, and `F` commutes with shifts.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DerivedCategory

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.ExtremalDegrees

universe u v w w'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type w} [Category.{w'} D] [Abelian D]

/-! ### Truncation comparisons on cohomology -/

/-- In degrees below `c` the canonical map `τ^{<c}X ⟶ X` is invertible on cohomology. -/
theorem isIso_homology_truncLT (c i : ℤ) (hi : i < c) (X : DerivedCategory C) :
    IsIso ((homologyFunctor C i).map ((TStructure.t.truncLTι c).app X)) := by
  have hT := TStructure.t.triangleLTGE_distinguished c X
  have : Epi ((homologyFunctor C i).map
      ((TStructure.t.triangleLTGE c).obj X).mor₁) := by
    rw [HomologySequence.epi_homologyMap_mor₁_iff _ hT i]
    exact (isZero_of_isGE _ c i hi).eq_of_tgt _ _
  have : Mono ((homologyFunctor C i).map
      ((TStructure.t.triangleLTGE c).obj X).mor₁) := by
    rw [HomologySequence.mono_homologyMap_mor₁_iff _ hT (i - 1) i (by omega)]
    exact (isZero_of_isGE _ c (i - 1) (by omega)).eq_of_src _ _
  change IsIso ((homologyFunctor C i).map ((TStructure.t.triangleLTGE c).obj X).mor₁)
  exact isIso_of_mono_of_epi _

/-- In degrees at least `c` the canonical map `X ⟶ τ^{≥c}X` is invertible on cohomology. -/
theorem isIso_homology_truncGE (c i : ℤ) (hi : c ≤ i) (X : DerivedCategory C) :
    IsIso ((homologyFunctor C i).map ((TStructure.t.truncGEπ c).app X)) := by
  have hT := TStructure.t.triangleLTGE_distinguished c X
  have : Epi ((homologyFunctor C i).map
      ((TStructure.t.triangleLTGE c).obj X).mor₂) := by
    rw [HomologySequence.epi_homologyMap_mor₂_iff _ hT i (i + 1) rfl]
    exact (isZero_of_isLE ((TStructure.t.triangleLTGE c).obj X).obj₁ (c - 1) (i + 1)
      (by omega)).eq_of_tgt _ _
  have : Mono ((homologyFunctor C i).map
      ((TStructure.t.triangleLTGE c).obj X).mor₂) := by
    rw [HomologySequence.mono_homologyMap_mor₂_iff _ hT i]
    exact (isZero_of_isLE ((TStructure.t.triangleLTGE c).obj X).obj₁ (c - 1) i
      (by omega)).eq_of_src _ _
  change IsIso ((homologyFunctor C i).map ((TStructure.t.triangleLTGE c).obj X).mor₂)
  exact isIso_of_mono_of_epi _

/-! ### The single complex in degree `a` as a shift -/

/-- `F` applied to the single complex of `N` in degree `a` is the shift by `-a` of `F` applied to
the single complex of `N` in degree zero. -/
def mapSingleShiftIso (F : DerivedCategory C ⥤ DerivedCategory D) [F.CommShift ℤ] (N : C)
    (a : ℤ) :
    F.obj ((singleFunctor C a).obj N) ≅ (F.obj ((singleFunctor C 0).obj N))⟦-a⟧ :=
  F.mapIso (((singleFunctors C).shiftIso (-a) a 0 (by omega)).app N).symm ≪≫
    (F.commShiftIso (-a)).app ((singleFunctor C 0).obj N)

/-! ### The two bounds -/

/-- An exact functor which is right `t`-exact, up to the degree shift, on the single complex of
the one nonvanishing cohomology module of `X` is right `t`-exact on `X`. -/
theorem isLE_map_of_single_homology (F : DerivedCategory C ⥤ DerivedCategory D) [F.CommShift ℤ]
    (X : DerivedCategory C) (c b : ℤ) [X.IsGE c] [X.IsLE c]
    (h : (F.obj ((singleFunctor C 0).obj ((homologyFunctor C c).obj X))).IsLE (b - c)) :
    (F.obj X).IsLE b := by
  obtain ⟨Y, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X c
  have := TStructure.t.isLE_shift
    (F.obj ((singleFunctor C 0).obj ((homologyFunctor C c).obj X))) (b - c) (-c) b (by omega)
  exact TStructure.t.isLE_of_iso ((mapSingleShiftIso F ((homologyFunctor C c).obj X) c).symm ≪≫
    F.mapIso ((singleFunctor C c).mapIso ((homologyFunctor C c).mapIso e ≪≫
      (singleFunctorCompHomologyFunctorIso C c).app Y) ≪≫ e.symm)) b

/-- An exact functor which is left `t`-exact, up to the degree shift, on the single complex of
the one nonvanishing cohomology module of `X` is left `t`-exact on `X`. -/
theorem isGE_map_of_single_homology (F : DerivedCategory C ⥤ DerivedCategory D) [F.CommShift ℤ]
    (X : DerivedCategory C) (c b : ℤ) [X.IsGE c] [X.IsLE c]
    (h : (F.obj ((singleFunctor C 0).obj ((homologyFunctor C c).obj X))).IsGE (b - c)) :
    (F.obj X).IsGE b := by
  obtain ⟨Y, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X c
  have := TStructure.t.isGE_shift
    (F.obj ((singleFunctor C 0).obj ((homologyFunctor C c).obj X))) (b - c) (-c) b (by omega)
  exact TStructure.t.isGE_of_iso ((mapSingleShiftIso F ((homologyFunctor C c).obj X) c).symm ≪≫
    F.mapIso ((singleFunctor C c).mapIso ((homologyFunctor C c).mapIso e ≪≫
      (singleFunctorCompHomologyFunctorIso C c).app Y) ≪≫ e.symm)) b

/-- `F` applied to the single complex of the cohomology, in degree `i`, of the source and of the
target of a map inducing an isomorphism on `H^i`. -/
private def mapSingleHomologyIso (F : DerivedCategory C ⥤ DerivedCategory D)
    {X Y : DerivedCategory C} (f : X ⟶ Y) (i : ℤ) [IsIso ((homologyFunctor C i).map f)] :
    F.obj ((singleFunctor C 0).obj ((homologyFunctor C i).obj X)) ≅
      F.obj ((singleFunctor C 0).obj ((homologyFunctor C i).obj Y)) :=
  F.mapIso ((singleFunctor C 0).mapIso (asIso ((homologyFunctor C i).map f)))

/-- `F` kills the single complex of a vanishing cohomology module. -/
private theorem isZero_map_single_homology (F : DerivedCategory C ⥤ DerivedCategory D)
    [F.CommShift ℤ] [F.IsTriangulated] (Y : DerivedCategory C) (i : ℤ)
    (hY : IsZero ((homologyFunctor C i).obj Y)) :
    IsZero (F.obj ((singleFunctor C 0).obj ((homologyFunctor C i).obj Y))) :=
  F.map_isZero ((singleFunctor C 0).map_isZero hY)

/-- Truncating `τ^{<b}` keeps an object bounded below by `a ≤ b + 1`. -/
private theorem isGE_truncLT_of_isGE (X : DerivedCategory C) (a b : ℤ) (hab : a ≤ b + 1)
    (hX : X.IsGE a) : ((TStructure.t.truncLT b).obj X).IsGE a := by
  have := hX
  have h₂ : TStructure.t.IsGE ((TStructure.t.triangleLTGE b).obj X).obj₂ a := hX
  have h₃ : TStructure.t.IsGE (((TStructure.t.triangleLTGE b).obj X).obj₃⟦(-1 : ℤ)⟧) a := by
    have := TStructure.t.isGE_shift ((TStructure.t.triangleLTGE b).obj X).obj₃ b (-1) (b + 1)
    exact TStructure.t.isGE_of_ge _ a (b + 1)
  exact TStructure.t.isGE₂ ((TStructure.t.triangleLTGE b).obj X).invRotate
    (inv_rot_of_distTriang _ (TStructure.t.triangleLTGE_distinguished b X)) a h₃ h₂

/-- Truncating `τ^{≥c}` keeps an object bounded above by `b` whenever `c ≤ b + 2`. -/
private theorem isLE_truncGE_of_isLE (X : DerivedCategory C) (b c : ℤ) (hcb : c ≤ b + 2)
    (hX : X.IsLE b) : ((TStructure.t.truncGE c).obj X).IsLE b := by
  have := hX
  have h₂ : TStructure.t.IsLE ((TStructure.t.triangleLTGE c).obj X).obj₂ b := hX
  have h₃ : TStructure.t.IsLE (((TStructure.t.triangleLTGE c).obj X).obj₁⟦(1 : ℤ)⟧) b := by
    have := TStructure.t.isLE_shift ((TStructure.t.triangleLTGE c).obj X).obj₁ (c - 1) 1 (c - 2)
    exact TStructure.t.isLE_of_le _ (c - 2) b
  exact TStructure.t.isLE₂ ((TStructure.t.triangleLTGE c).obj X).rotate
    (rot_of_distTriang _ (TStructure.t.triangleLTGE_distinguished c X)) b h₂ h₃

private theorem isLE_map_of_homology_aux (F : DerivedCategory C ⥤ DerivedCategory D)
    [F.CommShift ℤ] [F.IsTriangulated] (b c : ℤ) (n : ℕ) (X : DerivedCategory C)
    [X.IsGE c] [hle : X.IsLE (c + n)]
    (h : ∀ i : ℤ, (F.obj ((singleFunctor C 0).obj ((homologyFunctor C i).obj X))).IsLE (b - i)) :
    (F.obj X).IsLE b := by
  induction n generalizing X with
  | zero =>
      have : X.IsLE c := by simpa only [Nat.cast_zero, add_zero] using hle
      exact isLE_map_of_single_homology F X c b (h c)
  | succ n ih =>
      let d : ℤ := c + n + 1
      have h₁ : (F.obj ((TStructure.t.truncLT d).obj X)).IsLE b := by
        have : ((TStructure.t.truncLT d).obj X).IsLE (c + (n : ℤ)) :=
          TStructure.t.isLE_of_le _ (d - 1) _ (by dsimp [d]; omega)
        apply ih
        intro i
        by_cases hi : i < d
        · have := isIso_homology_truncLT d i hi X
          have := h i
          exact TStructure.t.isLE_of_iso
            (mapSingleHomologyIso (Y := X) F ((TStructure.t.truncLTι d).app X) i).symm (b - i)
        · exact TStructure.t.isLE_of_isZero (isZero_map_single_homology F _ i
            (isZero_of_isLE _ (d - 1) i (by omega))) _
      have : X.IsLE d :=
        TStructure.t.isLE_of_le _ (c + (n + 1 : ℕ)) d (by dsimp [d]; omega)
      have h₃ : (F.obj ((TStructure.t.truncGE d).obj X)).IsLE b := by
        apply isLE_map_of_single_homology F _ d b
        have := isIso_homology_truncGE d d le_rfl X
        have := h d
        exact TStructure.t.isLE_of_iso
          (mapSingleHomologyIso (X := X) F ((TStructure.t.truncGEπ d).app X) d) (b - d)
      exact TStructure.t.isLE₂ (F.mapTriangle.obj ((TStructure.t.triangleLTGE d).obj X))
        (F.map_distinguished _ (TStructure.t.triangleLTGE_distinguished d X)) b h₁ h₃

private theorem isGE_map_of_homology_aux (F : DerivedCategory C ⥤ DerivedCategory D)
    [F.CommShift ℤ] [F.IsTriangulated] (b c : ℤ) (n : ℕ) (X : DerivedCategory C)
    [X.IsGE c] [hle : X.IsLE (c + n)]
    (h : ∀ i : ℤ, (F.obj ((singleFunctor C 0).obj ((homologyFunctor C i).obj X))).IsGE (b - i)) :
    (F.obj X).IsGE b := by
  induction n generalizing X with
  | zero =>
      have : X.IsLE c := by simpa only [Nat.cast_zero, add_zero] using hle
      exact isGE_map_of_single_homology F X c b (h c)
  | succ n ih =>
      let d : ℤ := c + n + 1
      have h₁ : (F.obj ((TStructure.t.truncLT d).obj X)).IsGE b := by
        have : ((TStructure.t.truncLT d).obj X).IsLE (c + (n : ℤ)) :=
          TStructure.t.isLE_of_le _ (d - 1) _ (by dsimp [d]; omega)
        apply ih
        intro i
        by_cases hi : i < d
        · have := isIso_homology_truncLT d i hi X
          have := h i
          exact TStructure.t.isGE_of_iso
            (mapSingleHomologyIso (Y := X) F ((TStructure.t.truncLTι d).app X) i).symm (b - i)
        · exact TStructure.t.isGE_of_isZero (isZero_map_single_homology F _ i
            (isZero_of_isLE _ (d - 1) i (by omega))) _
      have : X.IsLE d :=
        TStructure.t.isLE_of_le _ (c + (n + 1 : ℕ)) d (by dsimp [d]; omega)
      have h₃ : (F.obj ((TStructure.t.truncGE d).obj X)).IsGE b := by
        apply isGE_map_of_single_homology F _ d b
        have := isIso_homology_truncGE d d le_rfl X
        have := h d
        exact TStructure.t.isGE_of_iso
          (mapSingleHomologyIso (X := X) F ((TStructure.t.truncGEπ d).app X) d) (b - d)
      exact TStructure.t.isGE₂ (F.mapTriangle.obj ((TStructure.t.triangleLTGE d).obj X))
        (F.map_distinguished _ (TStructure.t.triangleLTGE_distinguished d X)) b h₁ h₃

/-- **The right `t`-exactness bound.**  For `X` with cohomology concentrated in `[c, d]`, an
exact functor which carries each `H^i(X)[0]` into `D^{≤ b - i}` carries `X` into `D^{≤ b}`. -/
theorem isLE_map_of_homology (F : DerivedCategory C ⥤ DerivedCategory D)
    [F.CommShift ℤ] [F.IsTriangulated] (X : DerivedCategory C) (c d b : ℤ)
    (hc : X.IsGE c) (hd : X.IsLE d)
    (h : ∀ i : ℤ, (F.obj ((singleFunctor C 0).obj ((homologyFunctor C i).obj X))).IsLE (b - i)) :
    (F.obj X).IsLE b := by
  by_cases hcd : c ≤ d
  · have : X.IsLE (c + ((d - c).toNat : ℤ)) := TStructure.t.isLE_of_le _ d _ (by omega)
    exact isLE_map_of_homology_aux F b c (d - c).toNat X h
  · apply TStructure.t.isLE_of_isZero
    exact F.map_isZero (TStructure.t.isZero X d c (by omega))

/-- **The left `t`-exactness bound.**  For `X` with cohomology concentrated in `[c, d]`, an exact
functor which carries each `H^i(X)[0]` into `D^{≥ b - i}` carries `X` into `D^{≥ b}`. -/
theorem isGE_map_of_homology (F : DerivedCategory C ⥤ DerivedCategory D)
    [F.CommShift ℤ] [F.IsTriangulated] (X : DerivedCategory C) (c d b : ℤ)
    (hc : X.IsGE c) (hd : X.IsLE d)
    (h : ∀ i : ℤ, (F.obj ((singleFunctor C 0).obj ((homologyFunctor C i).obj X))).IsGE (b - i)) :
    (F.obj X).IsGE b := by
  by_cases hcd : c ≤ d
  · have : X.IsLE (c + ((d - c).toNat : ℤ)) := TStructure.t.isLE_of_le _ d _ (by omega)
    exact isGE_map_of_homology_aux F b c (d - c).toNat X h
  · apply TStructure.t.isGE_of_isZero
    exact F.map_isZero (TStructure.t.isZero X d c (by omega))

/-! ### The nonvanishing -/

/-- A monomorphism out of an object with a nonzero source has a nonzero target. -/
theorem not_isZero_of_mono {Z : Type w} [Category.{w'} Z] [Abelian Z] {U V : Z} (f : U ⟶ V)
    (hf : Mono f) (hU : ¬ IsZero U) : ¬ IsZero V := by
  intro hV
  refine hU ((IsZero.iff_id_eq_zero U).2 ?_)
  rw [← cancel_mono f, Category.id_comp, hV.eq_of_tgt f 0, zero_comp]

/-- An epimorphism with a nonzero target has a nonzero source. -/
theorem not_isZero_of_epi {Z : Type w} [Category.{w'} Z] [Abelian Z] {U V : Z} (f : U ⟶ V)
    (hf : Epi f) (hV : ¬ IsZero V) : ¬ IsZero U := by
  intro hU
  refine hV ((IsZero.iff_id_eq_zero V).2 ?_)
  rw [← cancel_epi f, Category.comp_id, hU.eq_of_src f 0, zero_comp]

/-- **The nonvanishing at the bottom.**  Let `X` have no cohomology below `a` and suppose that
`F(τ^{≥ a+1}X)` has none below `n + 1`.  If the `n`-th cohomology of `F` at the bottom truncation
`τ^{<a+1}X` of `X` — the single complex of `H^a(X)` in degree `a` — is nonzero, then so is the
`n`-th cohomology of `F(X)`.

The connecting map into `H^n(F(τ^{<a+1}X))` comes from `H^{n-1}(F(τ^{≥ a+1}X))`, which vanishes;
so `H^n(F(τ^{<a+1}X)) ⟶ H^n(F(X))` is injective. -/
theorem not_isZero_homology_map_of_isGE (F : DerivedCategory C ⥤ DerivedCategory D)
    [F.CommShift ℤ] [F.IsTriangulated] (X : DerivedCategory C) (a n : ℤ)
    (hup : (F.obj ((TStructure.t.truncGE (a + 1)).obj X)).IsGE (n + 1))
    (hne : ¬ IsZero ((homologyFunctor D n).obj
      (F.obj ((TStructure.t.truncLT (a + 1)).obj X)))) :
    ¬ IsZero ((homologyFunctor D n).obj (F.obj X)) := by
  have hT := F.map_distinguished _ (TStructure.t.triangleLTGE_distinguished (a + 1) X)
  have hmono : Mono ((homologyFunctor D n).map
      (F.mapTriangle.obj ((TStructure.t.triangleLTGE (a + 1)).obj X)).mor₁) := by
    rw [HomologySequence.mono_homologyMap_mor₁_iff _ hT (n - 1) n (by omega)]
    exact (isZero_of_isGE (F.obj ((TStructure.t.truncGE (a + 1)).obj X)) (n + 1) (n - 1)
      (by omega) (hX := hup)).eq_of_src _ _
  exact not_isZero_of_mono ((homologyFunctor D n).map
    (F.mapTriangle.obj ((TStructure.t.triangleLTGE (a + 1)).obj X)).mor₁) hmono hne

/-- **The nonvanishing at the top.**  Let `X` have no cohomology above `b` and suppose that
`F(τ^{<b}X)` has none above `n - 1`.  If the `n`-th cohomology of `F` at the top truncation
`τ^{≥b}X` of `X` — the single complex of `H^b(X)` in degree `b` — is nonzero, then so is the
`n`-th cohomology of `F(X)`. -/
theorem not_isZero_homology_map_of_isLE (F : DerivedCategory C ⥤ DerivedCategory D)
    [F.CommShift ℤ] [F.IsTriangulated] (X : DerivedCategory C) (b n : ℤ)
    (hlow : (F.obj ((TStructure.t.truncLT b).obj X)).IsLE (n - 1))
    (hne : ¬ IsZero ((homologyFunctor D n).obj
      (F.obj ((TStructure.t.truncGE b).obj X)))) :
    ¬ IsZero ((homologyFunctor D n).obj (F.obj X)) := by
  have hT := F.map_distinguished _ (TStructure.t.triangleLTGE_distinguished b X)
  have hepi : Epi ((homologyFunctor D n).map
      (F.mapTriangle.obj ((TStructure.t.triangleLTGE b).obj X)).mor₂) := by
    rw [HomologySequence.epi_homologyMap_mor₂_iff _ hT n (n + 1) rfl]
    exact (isZero_of_isLE (F.obj ((TStructure.t.truncLT b).obj X)) (n - 1) (n + 1)
      (by omega) (hX := hlow)).eq_of_tgt _ _
  exact not_isZero_of_epi ((homologyFunctor D n).map
    (F.mapTriangle.obj ((TStructure.t.triangleLTGE b).obj X)).mor₂) hepi hne

/-! ### The extremal degrees add -/

/-- Nonvanishing of the cohomology of `F` at a single complex transports from degree zero to
degree `a`, the cohomological index shifting by `a`. -/
theorem not_isZero_homology_map_single_shift (F : DerivedCategory C ⥤ DerivedCategory D)
    [F.CommShift ℤ] (N : C) (a n n' : ℤ) (h : n' = n + a)
    (hne : ¬ IsZero ((homologyFunctor D n).obj (F.obj ((singleFunctor C 0).obj N)))) :
    ¬ IsZero ((homologyFunctor D n').obj (F.obj ((singleFunctor C a).obj N))) := by
  intro hz
  refine hne (IsZero.of_iso hz ?_)
  exact (((homologyFunctor D n').mapIso (mapSingleShiftIso F N a)) ≪≫
    ((homologyFunctor D 0).shiftIso (-a) n' n (by omega)).app _).symm

/-- The bottom truncation of an object with no cohomology below `a` is concentrated in degree
`a`: it is bounded above by `a` by construction, and bounded below by `a` because the object is
and the complementary truncation is bounded below by `a + 1`. -/
theorem isGE_truncLT_succ (X : DerivedCategory C) (a : ℤ) (hX : X.IsGE a) :
    ((TStructure.t.truncLT (a + 1)).obj X).IsGE a :=
  isGE_truncLT_of_isGE X a (a + 1) (by omega) hX

/-- The top truncation of an object with no cohomology above `b` is concentrated in degree `b`. -/
theorem isLE_truncGE (X : DerivedCategory C) (b : ℤ) (hX : X.IsLE b) :
    ((TStructure.t.truncGE b).obj X).IsLE b :=
  isLE_truncGE_of_isLE X b b (by omega) hX

/-- The bottom truncation of `X`, for `X` with no cohomology below `a`, is the single complex of
`H^a(X)` in degree `a`. -/
theorem nonempty_iso_truncLT_succ_singleFunctor (X : DerivedCategory C) (a : ℤ) (hX : X.IsGE a) :
    Nonempty ((TStructure.t.truncLT (a + 1)).obj X ≅
      (singleFunctor C a).obj ((homologyFunctor C a).obj X)) := by
  have h₁ := isGE_truncLT_succ X a hX
  have h₂ : ((TStructure.t.truncLT (a + 1)).obj X).IsLE a :=
    TStructure.t.isLE_of_le _ (a + 1 - 1) a
  obtain ⟨Y, ⟨e⟩⟩ :=
    DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
      ((TStructure.t.truncLT (a + 1)).obj X) a
  have := isIso_homology_truncLT (a + 1) a (by omega) X
  refine ⟨e ≪≫ (singleFunctor C a).mapIso
    (((singleFunctorCompHomologyFunctorIso C a).app Y).symm ≪≫
      ((homologyFunctor C a).mapIso e).symm ≪≫
      asIso ((homologyFunctor C a).map ((TStructure.t.truncLTι (a + 1)).app X)))⟩

/-- The top truncation of `X`, for `X` with no cohomology above `b`, is the single complex of
`H^b(X)` in degree `b`. -/
theorem nonempty_iso_truncGE_singleFunctor (X : DerivedCategory C) (b : ℤ) (hX : X.IsLE b) :
    Nonempty ((TStructure.t.truncGE b).obj X ≅
      (singleFunctor C b).obj ((homologyFunctor C b).obj X)) := by
  have h₁ := isLE_truncGE X b hX
  have h₂ : ((TStructure.t.truncGE b).obj X).IsGE b := inferInstance
  obtain ⟨Y, ⟨e⟩⟩ :=
    DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
      ((TStructure.t.truncGE b).obj X) b
  have := isIso_homology_truncGE b b le_rfl X
  refine ⟨e ≪≫ (singleFunctor C b).mapIso
    (((singleFunctorCompHomologyFunctorIso C b).app Y).symm ≪≫
      ((homologyFunctor C b).mapIso e).symm ≪≫
      (asIso ((homologyFunctor C b).map ((TStructure.t.truncGEπ b).app X))).symm)⟩

/-- **The extremal cohomological degrees of `F(X)` are those of `X` shifted by those of `F` on
the single complexes of the cohomology of `X`.**

Let `X` have cohomology concentrated in `[a, b]`, and let `F` carry the single complex in degree
zero of each cohomology module of `X` into `D^{[c, d]}`.  Then `F(X)` has cohomology concentrated
in `[a + c, b + d]`; and if moreover `F` has nonvanishing `c`-th cohomology at `H^a(X)[0]` and
nonvanishing `d`-th cohomology at `H^b(X)[0]`, then `F(X)` has nonvanishing cohomology in degrees
`a + c` and `b + d` — so those are exactly its bottom and top nonvanishing degrees.

The bounds are the truncation induction; the nonvanishing is the long exact sequence of the
truncation triangle at the two ends, where one of the two neighbours has already been bounded
away from the degree in question. -/
theorem extremalDegrees (F : DerivedCategory C ⥤ DerivedCategory D) [F.CommShift ℤ]
    [F.IsTriangulated] (X : DerivedCategory C) (a b c d : ℤ)
    (ha : X.IsGE a) (hb : X.IsLE b)
    (hGE : ∀ i : ℤ, (F.obj ((singleFunctor C 0).obj ((homologyFunctor C i).obj X))).IsGE c)
    (hLE : ∀ i : ℤ, (F.obj ((singleFunctor C 0).obj ((homologyFunctor C i).obj X))).IsLE d)
    (hbot : ¬ IsZero ((homologyFunctor D c).obj
      (F.obj ((singleFunctor C 0).obj ((homologyFunctor C a).obj X)))))
    (htop : ¬ IsZero ((homologyFunctor D d).obj
      (F.obj ((singleFunctor C 0).obj ((homologyFunctor C b).obj X))))) :
    (F.obj X).IsGE (a + c) ∧ (F.obj X).IsLE (b + d) ∧
      ¬ IsZero ((homologyFunctor D (a + c)).obj (F.obj X)) ∧
      ¬ IsZero ((homologyFunctor D (b + d)).obj (F.obj X)) := by
  have hzero : ∀ Y : DerivedCategory C, ∀ i : ℤ,
      IsZero ((homologyFunctor C i).obj Y) → ∀ n : ℤ,
      (F.obj ((singleFunctor C 0).obj ((homologyFunctor C i).obj Y))).IsGE n ∧
        (F.obj ((singleFunctor C 0).obj ((homologyFunctor C i).obj Y))).IsLE n :=
    fun Y i hY n => ⟨TStructure.t.isGE_of_isZero (isZero_map_single_homology F Y i hY) n,
      TStructure.t.isLE_of_isZero (isZero_map_single_homology F Y i hY) n⟩
  have hab : a ≤ b := by
    by_contra hcon
    have := hb
    exact hbot ((homologyFunctor D c).map_isZero
      (isZero_map_single_homology F X a (isZero_of_isLE X b a (by omega))))
  -- the two bounds, for `X` itself
  have hXGE : (F.obj X).IsGE (a + c) := by
    refine isGE_map_of_homology F X a b (a + c) ha hb fun i => ?_
    by_cases hi : a ≤ i
    · have := hGE i
      exact TStructure.t.isGE_of_ge _ (a + c - i) c (by omega)
    · have := ha
      exact (hzero X i (isZero_of_isGE X a i (by omega)) (a + c - i)).1
  have hXLE : (F.obj X).IsLE (b + d) := by
    refine isLE_map_of_homology F X a b (b + d) ha hb fun i => ?_
    by_cases hi : i ≤ b
    · have := hLE i
      exact TStructure.t.isLE_of_le _ d (b + d - i)
    · have := hb
      exact (hzero X i (isZero_of_isLE X b i (by omega)) (b + d - i)).2
  refine ⟨hXGE, hXLE, ?_, ?_⟩
  · -- the bottom
    refine not_isZero_homology_map_of_isGE F X a (a + c) ?_ ?_
    · have hGEup : ((TStructure.t.truncGE (a + 1)).obj X).IsGE (a + 1) := inferInstance
      have hLEup : ((TStructure.t.truncGE (a + 1)).obj X).IsLE b :=
        isLE_truncGE_of_isLE X b (a + 1) (by omega) hb
      refine isGE_map_of_homology F _ (a + 1) b (a + c + 1) hGEup hLEup fun i => ?_
      by_cases hi : a + 1 ≤ i
      · have := isIso_homology_truncGE (a + 1) i hi X
        have := hGE i
        have h4 : TStructure.t.IsGE
            (F.obj ((singleFunctor C 0).obj ((homologyFunctor C i).obj X))) (a + c + 1 - i) :=
          TStructure.t.isGE_of_ge _ (a + c + 1 - i) c (by omega)
        exact TStructure.t.isGE_of_iso
          (mapSingleHomologyIso (X := X) F ((TStructure.t.truncGEπ (a + 1)).app X) i)
          (a + c + 1 - i)
      · have := hGEup
        exact (hzero _ i (isZero_of_isGE _ (a + 1) i (by omega)) (a + c + 1 - i)).1
    · obtain ⟨e⟩ := nonempty_iso_truncLT_succ_singleFunctor X a ha
      intro hz
      refine not_isZero_homology_map_single_shift F ((homologyFunctor C a).obj X) a c (a + c)
        (by omega) hbot ?_
      exact IsZero.of_iso hz ((homologyFunctor D (a + c)).mapIso (F.mapIso e)).symm
  · -- the top
    refine not_isZero_homology_map_of_isLE F X b (b + d) ?_ ?_
    · have hGElow : ((TStructure.t.truncLT b).obj X).IsGE a :=
        isGE_truncLT_of_isGE X a b (by omega) ha
      have hLElow : ((TStructure.t.truncLT b).obj X).IsLE (b - 1) :=
        TStructure.t.isLE_of_le _ (b - 1) (b - 1)
      refine isLE_map_of_homology F _ a (b - 1) (b + d - 1) hGElow hLElow fun i => ?_
      by_cases hi : i < b
      · have := isIso_homology_truncLT b i hi X
        have := hLE i
        have h6 : TStructure.t.IsLE
            (F.obj ((singleFunctor C 0).obj ((homologyFunctor C i).obj X))) (b + d - 1 - i) :=
          TStructure.t.isLE_of_le _ d (b + d - 1 - i) (by omega)
        exact TStructure.t.isLE_of_iso
          (mapSingleHomologyIso (Y := X) F ((TStructure.t.truncLTι b).app X) i).symm (b + d - 1 - i)
      · have := hLElow
        exact (hzero _ i (isZero_of_isLE _ (b - 1) i (by omega)) (b + d - 1 - i)).2
    · obtain ⟨e⟩ := nonempty_iso_truncGE_singleFunctor X b hb
      intro hz
      refine not_isZero_homology_map_single_shift F ((homologyFunctor C b).obj X) b d (b + d)
        (by omega) htop ?_
      exact IsZero.of_iso hz ((homologyFunctor D (b + d)).mapIso (F.mapIso e)).symm

/-! ### Reading the extremal degrees back off a fixed object -/

/-- **An object isomorphic to one whose window it widens at the top has not widened it at all.**
Let `X` lie in `D^{≤ b}` with `H^b(X) ≠ 0` — so `b` is the top nonvanishing degree of `X` — let
`Y ≅ X`, and let `Y` lie in `D^{≤ b + d}` with `H^{b + d}(Y) ≠ 0`, so that `b + d` is the top
nonvanishing degree of `Y`.  Then `d = 0`.

Two inequalities: the isomorphism puts `X` in `D^{≤ b + d}`, which with `H^b(X) ≠ 0` forces
`b ≤ b + d`; and `H^{b + d}(Y) ≠ 0` with `X` in `D^{≤ b}` forces `b + d ≤ b`.

**Nothing below the top is used** — no lower bound on `X`, no nonvanishing at a bottom degree,
no bound on `Y` from below.  That is what makes it the reader for the one-sided computation:
`StacksDraft.ExtremalDegrees.extremalDegrees_top` of
`StacksFrontier.Homology.Tor.ExtremalDegreesTop` produces exactly `hLE` and `hd` for an `X` that is
bounded above only, and the two-sided
`StacksDraft.ExtremalDegrees.extremalDegrees_eq_zero_of_iso` is this statement together with its
mirror at the bottom. -/
theorem eq_zero_of_isLE_of_iso (X Y : DerivedCategory C) (b d : ℤ) (hb : X.IsLE b)
    (htop : ¬ IsZero ((homologyFunctor C b).obj X))
    (e : Y ≅ X) (hLE : Y.IsLE (b + d))
    (hd : ¬ IsZero ((homologyFunctor C (b + d)).obj Y)) :
    d = 0 := by
  have hXLE : X.IsLE (b + d) := TStructure.t.isLE_of_iso e (b + d)
  refine le_antisymm ?_ ?_
  · -- `d ≤ 0`: otherwise `Y` has no cohomology in degree `b + d`
    by_contra hcon
    exact hd (IsZero.of_iso (isZero_of_isLE X b (b + d) (by omega) (hX := hb))
      ((homologyFunctor C (b + d)).mapIso e))
  · -- `0 ≤ d`: otherwise `X` has no cohomology in degree `b`
    by_contra hcon
    exact htop (isZero_of_isLE X (b + d) b (by omega) (hX := hXLE))

/-- **An object isomorphic to one whose window it widens on both sides has not widened it at
all.**  Let `X` have cohomology concentrated in `[a, b]` and nonvanishing at both ends, let
`Y ≅ X`, and let `Y` have cohomology concentrated in `[a + c, b + d]` and nonvanishing in those
two degrees.  Then `c = 0` and `d = 0`.

Each equality is two inequalities, one from each pair of hypotheses.  For `c`: the isomorphism
puts `X` in `D^{≥ a+c}`, which with `H^a(X) ≠ 0` forces `c ≤ 0`; and `H^{a+c}(Y) ≠ 0` with `X` in
`D^{≥ a}` forces `0 ≤ c`.  The `d` half is `StacksDraft.ExtremalDegrees.eq_zero_of_isLE_of_iso`,
which uses none of the data at the bottom.

This is how `StacksDraft.ExtremalDegrees.extremalDegrees` is consumed by the rigidity argument of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessDuality`: at `Y = F(X)` for an exact `F` with
`F(X) ≅ X`, the conclusion is that the two extremal nonvanishing degrees of `F` on the single
complexes of the cohomology of `X` are both zero — so `F` carries those single complexes to
objects concentrated in degree zero. -/
theorem extremalDegrees_eq_zero_of_iso (X Y : DerivedCategory C) (a b c d : ℤ)
    (ha : X.IsGE a) (hb : X.IsLE b)
    (hbot : ¬ IsZero ((homologyFunctor C a).obj X))
    (htop : ¬ IsZero ((homologyFunctor C b).obj X))
    (e : Y ≅ X) (hGE : Y.IsGE (a + c)) (hLE : Y.IsLE (b + d))
    (hc : ¬ IsZero ((homologyFunctor C (a + c)).obj Y))
    (hd : ¬ IsZero ((homologyFunctor C (b + d)).obj Y)) :
    c = 0 ∧ d = 0 := by
  have hXGE : X.IsGE (a + c) := TStructure.t.isGE_of_iso e (a + c)
  refine ⟨le_antisymm ?_ ?_, eq_zero_of_isLE_of_iso X Y b d hb htop e hLE hd⟩
  · -- `c ≤ 0`: otherwise `X` has no cohomology in degree `a`
    by_contra hcon
    exact hbot (isZero_of_isGE X (a + c) a (by omega) (hX := hXGE))
  · -- `0 ≤ c`: otherwise `Y` has no cohomology in degree `a + c`
    by_contra hcon
    exact hc (IsZero.of_iso (isZero_of_isGE X a (a + c) (by omega) (hX := ha))
      ((homologyFunctor C (a + c)).mapIso e))

end StacksDraft.ExtremalDegrees

end
