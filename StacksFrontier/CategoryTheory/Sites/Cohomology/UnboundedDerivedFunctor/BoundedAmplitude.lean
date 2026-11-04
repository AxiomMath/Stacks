module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.Exactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGESuccTriangle
public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedCriterion

/-!
# Vanishing of a right derived functor on a bounded object, from its cohomology objects

Let `A` be a Grothendieck abelian category with enough injectives, let `F : A ⥤ B` be an additive
functor and let `RF : D(A) ⥤ D(B)` be its unbounded right derived functor. Let `E` be an object of
`D(A)` with no cohomology below some degree, and let `d` be an integer such that
`R^p F (H^j(E)) = 0` whenever `j + p > d`. Then `H^n(RF(E)) = 0` for every `n > d` and, if `E`
for every truncation of `E` from above. No upper bound on `E` is needed.

This is the vanishing that a spectral sequence `E_2^{p, j} = R^p F (H^j(E)) ⇒ H^{p + j}(RF(E))`
would give, obtained instead by induction along the truncation triangles
`τ_{≤ c}E ⟶ τ_{≤ c + 1}E ⟶ H^{c + 1}(E)[-c - 1]`: `RF` is exact, so the long exact cohomology
sequence of the image triangle propagates the vanishing, and on a single object placed in degree
`c + 1` the cohomology of `RF` in degree `n` is `R^{n - c - 1} F` of that object, or zero when
`n < c + 1` by left t-exactness.

## Main results

* `Stacks.DerivedFunctor.isZero_homology_totalRightDerived_truncLE`: the vanishing for every
  truncation `τ_{≤ c}E`.
* `Stacks.DerivedFunctor.isZero_homology_totalRightDerived_of_isLE`: the vanishing for a bounded
  `E`.
* `Stacks.DerivedFunctor.isZero_homology_totalRightDerived_of_isGE`: the vanishing for an `E`
  that is only bounded below.

## References

* [Stacks Project, Tag 015J](https://stacks.math.columbia.edu/tag/015J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.DerivedFunctor

universe wG wD wE v vB u uB

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{wG} A]
  [EnoughInjectives A] [HasDerivedCategory.{wD} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wE} B]

/-- The cohomology of `RF` applied to an object placed in degree `c` vanishes in degree `n`
as soon as `R^{n - c} F` vanishes on that object, the case `n < c` being left t-exactness. -/
lemma isZero_homology_totalRightDerived_single (F : A ⥤ B) [F.Additive] (M : A) (c n : ℤ)
    (hM : ∀ p : ℕ, (p : ℤ) = n - c → IsZero ((F.rightDerived p).obj M)) :
    IsZero ((DerivedCategory.homologyFunctor B n).obj
      ((totalRightDerived F).obj ((DerivedCategory.singleFunctor A c).obj M))) := by
  rcases lt_or_ge n c with h | h
  · exact isZero_homology_totalRightDerived_obj F _ c n h
  · obtain ⟨p, hp⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ n - c by omega)
    exact (hM p hp.symm).of_iso
      (homologyTotalRightDerivedSingleShiftIso F (totalRightDerived F)
        ((homotopyMap F).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
        Stacks.Injectives.exists_kInjective_resolution_of_grothendieck M c n p hp)

omit [EnoughInjectives A] in
/-- The unbounded right derived functor `RF` admits a shift by `ℤ` making it triangulated. -/
lemma exists_isTriangulated_totalRightDerived (F : A ⥤ B) [F.Additive] :
    ∃ _ : (totalRightDerived F).CommShift ℤ, (totalRightDerived F).IsTriangulated := by
  let α := (homotopyMap F).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
  let := Functor.IsRightDerivedFunctor.commShift (totalRightDerived F) α
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ℤ
  exact ⟨inferInstance, isTriangulated_of_isRightDerivedFunctor
    Stacks.Injectives.exists_kInjective_resolution_of_grothendieck (homotopyMap F) _ α⟩

omit [EnoughInjectives A] in
/-- The cohomology of `RF` in degree `n` vanishes on the middle vertex of a distinguished triangle
as soon as it vanishes on the two outer vertices. -/
lemma isZero_homology_totalRightDerived_obj₂ (F : A ⥤ B) [F.Additive]
    (T : Triangle (DerivedCategory A)) (hT : T ∈ distTriang _) (n : ℤ)
    (h₁ : IsZero ((DerivedCategory.homologyFunctor B n).obj ((totalRightDerived F).obj T.obj₁)))
    (h₃ : IsZero ((DerivedCategory.homologyFunctor B n).obj ((totalRightDerived F).obj T.obj₃))) :
    IsZero ((DerivedCategory.homologyFunctor B n).obj ((totalRightDerived F).obj T.obj₂)) := by
  obtain ⟨_, _⟩ := exists_isTriangulated_totalRightDerived F
  exact ((DerivedCategory.homologyFunctor B n).map_distinguished_exact _
    ((totalRightDerived F).map_distinguished _ hT)).isZero_X₂ (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

/-- **Vanishing on the truncations from above.** If `E` has no cohomology below `a` and
`R^p F (H^j(E)) = 0` whenever `j + p > d`, then `H^n(RF(τ_{≤ c}E)) = 0` for every `n > d` and
every `c`. -/
theorem isZero_homology_totalRightDerived_truncLE (F : A ⥤ B) [F.Additive] (d : ℤ)
    (E : DerivedCategory A) (a : ℤ) [E.IsGE a]
    (hE : ∀ (j : ℤ) (p : ℕ), d < j + p →
      IsZero ((F.rightDerived p).obj ((DerivedCategory.homologyFunctor A j).obj E)))
    (c n : ℤ) (hn : d < n) :
    IsZero ((DerivedCategory.homologyFunctor B n).obj
      ((totalRightDerived F).obj ((DerivedCategory.TStructure.t.truncLE c).obj E))) := by
  obtain ⟨_, _⟩ := exists_isTriangulated_totalRightDerived F
  -- induction on the number of degrees between `a - 1` and `c`
  suffices h : ∀ N : ℕ, ∀ c : ℤ, c ≤ a - 1 + N → IsZero ((DerivedCategory.homologyFunctor B n).obj
      ((totalRightDerived F).obj ((DerivedCategory.TStructure.t.truncLE c).obj E))) from
    h (c - (a - 1)).toNat c (by omega)
  intro N
  induction N with
  | zero =>
    intro c hc
    exact Functor.map_isZero _ (Functor.map_isZero _
      (DerivedCategory.TStructure.t.isZero _ c a (by simp at hc; omega)))
  | succ N ih =>
    intro c hc
    rcases le_or_gt c (a - 1 + N) with h | h
    · exact ih c h
    · obtain rfl : c = a - 1 + N + 1 := by push_cast at hc; omega
      obtain ⟨g, δ, hT⟩ := DerivedCategory.exists_truncLESucc_triangle E (a - 1 + N)
      exact isZero_homology_totalRightDerived_obj₂ F _ hT n (ih _ le_rfl)
        (isZero_homology_totalRightDerived_single F _ _ n fun p hp => hE _ p (by omega))

/-- **Vanishing on a bounded object.** If `E` is concentrated in degrees `[a, b]` and
`R^p F (H^j(E)) = 0` whenever `j + p > d`, then `H^n(RF(E)) = 0` for every `n > d`. -/
theorem isZero_homology_totalRightDerived_of_isLE (F : A ⥤ B) [F.Additive] (d : ℤ)
    (E : DerivedCategory A) (a b : ℤ) [E.IsGE a] [E.IsLE b]
    (hE : ∀ (j : ℤ) (p : ℕ), d < j + p →
      IsZero ((F.rightDerived p).obj ((DerivedCategory.homologyFunctor A j).obj E)))
    (n : ℤ) (hn : d < n) :
    IsZero ((DerivedCategory.homologyFunctor B n).obj ((totalRightDerived F).obj E)) :=
  (isZero_homology_totalRightDerived_truncLE F d E a hE b n hn).of_iso
    ((DerivedCategory.homologyFunctor B n).mapIso ((totalRightDerived F).mapIso
      (asIso ((DerivedCategory.TStructure.t.truncLEι b).app E)).symm))

/-- **Vanishing on an object bounded below.** If `E` has no cohomology below `a` and
`R^p F (H^j(E)) = 0` whenever `j + p > d`, then `H^n(RF(E)) = 0` for every `n > d`.

In degree `n` only `τ_{≤ n}E` contributes: the third vertex of the truncation triangle
`τ_{≤ n}E ⟶ E ⟶ τ_{≥ n + 1}E` has derived image concentrated in degrees `≥ n + 1`, by left
t-exactness. -/
theorem isZero_homology_totalRightDerived_of_isGE (F : A ⥤ B) [F.Additive] (d : ℤ)
    (E : DerivedCategory A) (a : ℤ) [E.IsGE a]
    (hE : ∀ (j : ℤ) (p : ℕ), d < j + p →
      IsZero ((F.rightDerived p).obj ((DerivedCategory.homologyFunctor A j).obj E)))
    (n : ℤ) (hn : d < n) :
    IsZero ((DerivedCategory.homologyFunctor B n).obj ((totalRightDerived F).obj E)) :=
  isZero_homology_totalRightDerived_obj₂ F _
    (DerivedCategory.TStructure.t.triangleLEGE_distinguished n (n + 1) rfl E) n
    (isZero_homology_totalRightDerived_truncLE F d E a hE n n hn)
    (isZero_homology_totalRightDerived_obj F
      ((DerivedCategory.TStructure.t.truncGE (n + 1)).obj E) (n + 1) n (by omega))

end Stacks.DerivedFunctor

end
