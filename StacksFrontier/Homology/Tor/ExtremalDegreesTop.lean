module

public import StacksFrontier.Homology.Tor.ExtremalDegrees

/-!
# The extremal cohomological degree at the top alone, for an unbounded-below object

Let `F` be an exact functor between derived categories that is way-out right exact, carrying
`D^{≤ n}` into `D^{≤ n + p}` for a single `p` and every `n`. For an object `X` that is bounded
above and need not be bounded below, the top nonvanishing cohomological degree of `F(X)` is read
off that of `X`.

## Main results

* `StacksDraft.ExtremalDegrees.isLE_truncGE_of_isLE`: a top truncation of an object bounded
  above by `b` is bounded above by `b`, for any truncation degree `n ≤ b + 2`.
* `StacksDraft.ExtremalDegrees.isLE_map_of_homology_of_wayOut`: for `X` in `D^{≤ b}`, a way-out
  right exact `F` carrying each `H^i(X)[0]` into `D^{≤ d}` carries `X` into `D^{≤ b + d}`.
* `StacksDraft.ExtremalDegrees.extremalDegrees_top`: if moreover the cohomology of `F` at
  `H^b(X)[0]` is nonvanishing in degree `d`, then the cohomology of `F(X)` is nonvanishing in
  degree `b + d`.

## References

* [Stacks Project, Tag 0E2D](https://stacks.math.columbia.edu/tag/0E2D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DerivedCategory

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.ExtremalDegrees

universe u v w w'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type w} [Category.{w'} D] [Abelian D]

/-- If `X` is bounded above by `b` and `n ≤ b + 2`, then the top truncation `τ^{≥n}X` is bounded
above by `b`. -/
theorem isLE_truncGE_of_isLE (X : DerivedCategory C) (n b : ℤ) (hnb : n ≤ b + 2)
    (hX : X.IsLE b) : ((TStructure.t.truncGE n).obj X).IsLE b := by
  have h₃ : TStructure.t.IsLE
      (((TStructure.t.triangleLTGE n).obj X).obj₁⟦(1 : ℤ)⟧) b := by
    have := TStructure.t.isLE_shift ((TStructure.t.triangleLTGE n).obj X).obj₁ (n - 1) 1 (n - 2)
    exact TStructure.t.isLE_of_le _ (n - 2) b (by lia)
  exact TStructure.t.isLE₂ ((TStructure.t.triangleLTGE n).obj X).rotate
    (rot_of_distTriang _ (TStructure.t.triangleLTGE_distinguished n X)) b hX h₃

/-- If `F` carries the single complex of each cohomology object of `X` into `D^{≤ d}`, then it
does so for each cohomology object of the bottom truncation `τ^{<n}X`. -/
private theorem isLE_map_single_homology_truncLT (F : DerivedCategory C ⥤ DerivedCategory D)
    [F.CommShift ℤ] [F.IsTriangulated] (X : DerivedCategory C) (n d : ℤ)
    (h : ∀ i : ℤ, (F.obj ((singleFunctor C 0).obj ((homologyFunctor C i).obj X))).IsLE d)
    (i : ℤ) :
    (F.obj ((singleFunctor C 0).obj
      ((homologyFunctor C i).obj ((TStructure.t.truncLT n).obj X)))).IsLE d := by
  by_cases hi : i < n
  · have := isIso_homology_truncLT n i hi X
    have := h i
    let e : F.obj ((singleFunctor C 0).obj ((homologyFunctor C i).obj X)) ≅
        F.obj ((singleFunctor C 0).obj
          ((homologyFunctor C i).obj ((TStructure.t.truncLT n).obj X))) :=
      F.mapIso ((singleFunctor C 0).mapIso
        (asIso ((homologyFunctor C i).map ((TStructure.t.truncLTι n).app X))).symm)
    exact TStructure.t.isLE_of_iso e d
  · apply TStructure.t.isLE_of_isZero
    exact F.map_isZero ((singleFunctor C 0).map_isZero
      (isZero_of_isLE _ (n - 1) i (by lia)))

/-- Let `X` lie in `D^{≤ b}`, let `F` be exact and way-out right exact with slack `p`, carrying
`D^{≤ m}` into `D^{≤ m + p}` for every `m`, and let `F` carry the single complex of each
cohomology object of `X` into `D^{≤ d}`. Then `F(X)` lies in `D^{≤ b + d}`. -/
theorem isLE_map_of_homology_of_wayOut (F : DerivedCategory C ⥤ DerivedCategory D)
    [F.CommShift ℤ] [F.IsTriangulated] (X : DerivedCategory C) (b d p : ℤ) (hb : X.IsLE b)
    (hway : ∀ (Y : DerivedCategory C) (m : ℤ), Y.IsLE m → (F.obj Y).IsLE (m + p))
    (h : ∀ i : ℤ, (F.obj ((singleFunctor C 0).obj ((homologyFunctor C i).obj X))).IsLE d) :
    (F.obj X).IsLE (b + d) := by
  by_cases hpd : p ≤ d
  · have := hway X b hb
    exact TStructure.t.isLE_of_le _ (b + p) (b + d) (by lia)
  set n : ℤ := b + d + 1 - p with hn
  have h₁ : (F.obj ((TStructure.t.truncLT n).obj X)).IsLE (b + d) := by
    have := hway ((TStructure.t.truncLT n).obj X) (n - 1) inferInstance
    exact TStructure.t.isLE_of_le _ (n - 1 + p) (b + d) (by lia)
  have h₃ : (F.obj ((TStructure.t.truncGE n).obj X)).IsLE (b + d) := by
    refine isLE_map_of_homology F ((TStructure.t.truncGE n).obj X) n b (b + d) inferInstance
      (isLE_truncGE_of_isLE X n b (by lia) hb) fun i ↦ ?_
    by_cases hi : n ≤ i
    · have := isIso_homology_truncGE n i hi X
      let q : (homologyFunctor C i).obj X ≅
          (homologyFunctor C i).obj ((TStructure.t.truncGE n).obj X) :=
        asIso ((homologyFunctor C i).map ((TStructure.t.truncGEπ n).app X))
      by_cases hib : i ≤ b
      · have := h i
        have := TStructure.t.isLE_of_iso (F.mapIso ((singleFunctor C 0).mapIso q)) d
        exact TStructure.t.isLE_of_le _ d (b + d - i) (by lia)
      · apply TStructure.t.isLE_of_isZero
        exact F.map_isZero ((singleFunctor C 0).map_isZero
          (IsZero.of_iso (isZero_of_isLE X b i (by lia)) q.symm))
    · apply TStructure.t.isLE_of_isZero
      exact F.map_isZero ((singleFunctor C 0).map_isZero
        (isZero_of_isGE ((TStructure.t.truncGE n).obj X) n i (by lia)))
  exact TStructure.t.isLE₂ (F.mapTriangle.obj ((TStructure.t.triangleLTGE n).obj X))
    (F.map_distinguished _ (TStructure.t.triangleLTGE_distinguished n X)) (b + d) h₁ h₃

/-- Let `X` lie in `D^{≤ b}`, let `F` be exact and way-out right exact with slack `p`, let `F`
carry the single complex of each cohomology object of `X` into `D^{≤ d}`, and let the `d`-th
cohomology of `F` at `H^b(X)[0]` be nonzero. Then `F(X)` lies in `D^{≤ b + d}` and its cohomology
in degree `b + d` is nonzero, so `b + d` is its top nonvanishing degree. -/
theorem extremalDegrees_top (F : DerivedCategory C ⥤ DerivedCategory D) [F.CommShift ℤ]
    [F.IsTriangulated] (X : DerivedCategory C) (b d p : ℤ) (hb : X.IsLE b)
    (hway : ∀ (Y : DerivedCategory C) (m : ℤ), Y.IsLE m → (F.obj Y).IsLE (m + p))
    (h : ∀ i : ℤ, (F.obj ((singleFunctor C 0).obj ((homologyFunctor C i).obj X))).IsLE d)
    (htop : ¬ IsZero ((homologyFunctor D d).obj
      (F.obj ((singleFunctor C 0).obj ((homologyFunctor C b).obj X))))) :
    (F.obj X).IsLE (b + d) ∧ ¬ IsZero ((homologyFunctor D (b + d)).obj (F.obj X)) := by
  refine ⟨isLE_map_of_homology_of_wayOut F X b d p hb hway h, ?_⟩
  refine not_isZero_homology_map_of_isLE F X b (b + d) ?_ ?_
  · have := isLE_map_of_homology_of_wayOut F ((TStructure.t.truncLT b).obj X) (b - 1) d p
      inferInstance hway (isLE_map_single_homology_truncLT F X b d h)
    exact TStructure.t.isLE_of_le _ (b - 1 + d) (b + d - 1) (by lia)
  · intro hz
    obtain ⟨e⟩ := nonempty_iso_truncGE_singleFunctor X b hb
    exact not_isZero_homology_map_single_shift F ((homologyFunctor C b).obj X) b d (b + d)
      (by lia) htop (IsZero.of_iso hz ((homologyFunctor D (b + d)).mapIso (F.mapIso e)).symm)

end StacksDraft.ExtremalDegrees

end
