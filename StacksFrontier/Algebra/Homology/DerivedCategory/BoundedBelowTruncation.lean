module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNaturalTransformations
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle

/-!
# Truncation on the bounded below derived category

Let `C` be an abelian category with a derived category. The canonical t-structure on the
unbounded derived category `D(C)` restricts to the strictly full triangulated subcategory
`D⁺(C) = DerivedCategory.Plus C` of bounded below objects, and Mathlib records the restriction
as `DerivedCategory.Plus.TStructure.t`. Everything a dévissage argument on `D⁺(C)` needs is
therefore formally available — the truncation functors `τ_{≤n}` and `τ_{>n}`, the truncation
triangle, and the `IsLE`/`IsGE` bookkeeping — but only in terms of the t-structure, whereas the
cohomology of an object of `D⁺(C)` is computed by `DerivedCategory.Plus.homologyFunctor`. This
file supplies the missing bridge between the two, and then the dévissage principle it is for.

The three groups of results are:

* the translation between `IsGE`/`IsLE` and the vanishing of
  `DerivedCategory.Plus.homologyFunctor`, and the invertibility of a morphism of a distinguished
  triangle on cohomology in the degrees where the opposite vertex vanishes;
* the consequences for the truncation morphisms `τ_{≤n}K ⟶ K` and `K ⟶ τ_{>n}K`: each is
  invertible on cohomology in the degrees its target, resp.\ source, retains, which is what
  identifies `τ_{≤n}` as "the part of `K` in degrees `≤ n`";
* the dévissage principle: a strictly full triangulated subcategory of `D⁺(C)` which is stable
  under the shift and contains each cohomology object of `K` placed in degree zero contains `K`
  itself, as soon as `K` has cohomology in finitely many degrees.

## Main results

* `DerivedCategory.Plus.isGE_iff` and `DerivedCategory.Plus.isLE_iff`: boundedness below,
  resp.\ above, is the vanishing of cohomology in the degrees outside the bound.
* `DerivedCategory.Plus.isIso_homologyMap_mor₁_of_isGE₃` and
  `DerivedCategory.Plus.isIso_homologyMap_mor₂_of_isLE₁`: invertibility on cohomology of the
  morphisms of a distinguished triangle one of whose vertices is bounded away.
* `DerivedCategory.Plus.isIso_homologyMap_truncLEι_app` and
  `DerivedCategory.Plus.isIso_homologyMap_truncGTπ_app`: the truncation morphisms are invertible
  on cohomology in the expected range of degrees.
* `DerivedCategory.Plus.isGE_truncGT_obj_succ`: `τ_{>n}K` is bounded below by `n + 1`.
* `DerivedCategory.Plus.isGE_three_of_isIso_homologyMap_mor₁`: the third vertex of a
  distinguished triangle whose first morphism is invertible on cohomology in all degrees `≤ n`
  is bounded below by `n + 1`.
* `DerivedCategory.Plus.exists_iso_singleFunctor_obj_of_isGE_of_isLE`: an object with cohomology
  in a single degree is a single object there.
* `DerivedCategory.Plus.prop_of_isGE_of_isLE`: **the dévissage principle** for an object with
  cohomology in finitely many degrees.

## Implementation notes

`DerivedCategory.Plus.homologyFunctor C n` is by definition the composite of the inclusion
`DerivedCategory.Plus.ι` with `DerivedCategory.homologyFunctor C n`, and
`DerivedCategory.Plus.TStructure.t` is by definition the t-structure induced on the subcategory,
so every statement below about cohomology of objects of `D⁺(C)` is transported from `D(C)`
along the inclusion rather than reproved: the inclusion is fully faithful and triangulated, and
`DerivedCategory.Plus.isGE_ι_obj_iff` and `DerivedCategory.Plus.isLE_ι_obj_iff` say it detects
the two boundedness conditions. In particular nothing here needs the long exact sequence of
`DerivedCategory.Plus.homologyFunctor` as a homological functor in its own right.

The dévissage principle is stated for an `CategoryTheory.ObjectProperty` which is closed under
isomorphisms, stable under the shift and closed under the middle vertex of a distinguished
triangle, rather than for `CategoryTheory.ObjectProperty.IsTriangulated`, which also asks for a
zero object: the zero object is not used, and the extra condition is the awkward one to check
for the locus where a natural transformation is invertible.

## References

* [Stacks Project, Tag 0118](https://stacks.math.columbia.edu/tag/0118)
* [Stacks Project, Tag 08J5](https://stacks.math.columbia.edu/tag/08J5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated

universe v u

namespace DerivedCategory.Plus

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

section Boundedness

/-- **Boundedness below is the vanishing of cohomology in low degrees**: an object of `D⁺(C)`
is `≥ n` for the canonical t-structure exactly when its cohomology vanishes in all degrees
`< n`, [Stacks, Tag 0118]. -/
lemma isGE_iff (X : Plus C) (n : ℤ) :
    X.IsGE n ↔ ∀ i : ℤ, i < n → IsZero ((homologyFunctor C i).obj X) := by
  rw [← isGE_ι_obj_iff, DerivedCategory.isGE_iff]
  exact ⟨fun h i hi ↦ h i hi, fun h i hi ↦ h i hi⟩

/-- **Boundedness above is the vanishing of cohomology in high degrees**: an object of `D⁺(C)`
is `≤ n` for the canonical t-structure exactly when its cohomology vanishes in all degrees
`> n`, [Stacks, Tag 0118]. -/
lemma isLE_iff (X : Plus C) (n : ℤ) :
    X.IsLE n ↔ ∀ i : ℤ, n < i → IsZero ((homologyFunctor C i).obj X) := by
  rw [← isLE_ι_obj_iff, DerivedCategory.isLE_iff]
  exact ⟨fun h i hi ↦ h i hi, fun h i hi ↦ h i hi⟩

/-- The cohomology of a bounded below object of `D⁺(C)` vanishes below the bound, [Stacks,
Tag 0118]. -/
lemma isZero_homology_of_isGE' (X : Plus C) (n i : ℤ) (hi : i < n) [X.IsGE n] :
    IsZero ((homologyFunctor C i).obj X) :=
  (isGE_iff X n).1 inferInstance i hi

/-- The cohomology of a bounded above object of `D⁺(C)` vanishes above the bound, [Stacks,
Tag 0118]. -/
lemma isZero_homology_of_isLE' (X : Plus C) (n i : ℤ) (hi : n < i) [X.IsLE n] :
    IsZero ((homologyFunctor C i).obj X) :=
  (isLE_iff X n).1 inferInstance i hi

end Boundedness

section Triangles

/-- **In a distinguished triangle of `D⁺(C)` whose third vertex is bounded below by `n`, the
first morphism is invertible on cohomology in every degree below `n`.** In the long exact
sequence of the triangle the map `H^i(T₁) ⟶ H^i(T₂)` is surrounded by `H^{i-1}(T₃)` and
`H^i(T₃)`, both of which vanish, [Stacks, Tag 08J5]. -/
theorem isIso_homologyMap_mor₁_of_isGE₃ (T : Triangle (Plus C))
    (hT : T ∈ distTriang (Plus C)) (i n : ℤ) (hGE : T.obj₃.IsGE n) (hi : i < n) :
    IsIso ((homologyFunctor C i).map T.mor₁) := by
  have := hGE
  exact _root_.DerivedCategory.isIso_homologyMap_mor₁_of_isGE₃ (ι.mapTriangle.obj T)
    (ι.map_distinguished T hT) i n (inferInstanceAs ((ι.obj T.obj₃).IsGE n)) hi

/-- **In a distinguished triangle of `D⁺(C)` whose first vertex is bounded above by `n`, the
second morphism is invertible on cohomology in every degree above `n`.** In the long exact
sequence the map `H^i(T₂) ⟶ H^i(T₃)` is surrounded by `H^i(T₁)` and `H^{i+1}(T₁)`, both of
which vanish, [Stacks, Tag 08J5]. -/
theorem isIso_homologyMap_mor₂_of_isLE₁ (T : Triangle (Plus C))
    (hT : T ∈ distTriang (Plus C)) (i n : ℤ) (hLE : T.obj₁.IsLE n) (hi : n < i) :
    IsIso ((homologyFunctor C i).map T.mor₂) := by
  have := hLE
  exact _root_.DerivedCategory.isIso_homologyMap_mor₂_of_isLE₁ (ι.mapTriangle.obj T)
    (ι.map_distinguished T hT) i n (inferInstanceAs ((ι.obj T.obj₁).IsLE n)) hi

/-- **The third vertex of a distinguished triangle of `D⁺(C)` whose first morphism is
epimorphic on cohomology in every degree `≤ n` and monomorphic in every degree `≤ n + 1` is
bounded below by `n + 1`**, [Stacks, Tag 08J5]. In the long exact sequence `H^i(T₃)` is caught
between the two, and no more than that is used: surjectivity in degree `i` kills the map out of
`H^i(T₃)` and injectivity in degree `i + 1` makes the map into `H^i(T₃)` surjective, so
`H^i(T₃)` is zero.

This is the form the comparison of a change of topology needs: there the first morphism is
invertible on cohomology only up to degree `n`, and in degree `n + 1` it is merely
monomorphic. -/
theorem isGE_three_of_epi_of_mono_homologyMap_mor₁ (T : Triangle (Plus C))
    (hT : T ∈ distTriang (Plus C)) (n : ℤ)
    (hepi : ∀ i : ℤ, i ≤ n → Epi ((homologyFunctor C i).map T.mor₁))
    (hmono : ∀ i : ℤ, i ≤ n + 1 → Mono ((homologyFunctor C i).map T.mor₁)) :
    T.obj₃.IsGE (n + 1) := by
  have hd : ι.mapTriangle.obj T ∈ distTriang (DerivedCategory C) := ι.map_distinguished T hT
  rw [isGE_iff]
  intro i hi
  have h₁ : Epi ((DerivedCategory.homologyFunctor C i).map (ι.mapTriangle.obj T).mor₁) :=
    hepi i (by omega)
  have h₂ : Mono ((DerivedCategory.homologyFunctor C (i + 1)).map
      (ι.mapTriangle.obj T).mor₁) := hmono (i + 1) (by omega)
  have hβ : (DerivedCategory.homologyFunctor C i).map (ι.mapTriangle.obj T).mor₂ = 0 := by
    rw [← DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff _ hd i]
    exact h₁
  have hδ : DerivedCategory.HomologySequence.δ (ι.mapTriangle.obj T) i (i + 1) rfl = 0 :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff _ hd i (i + 1) rfl).1 h₂
  have : Epi ((DerivedCategory.homologyFunctor C i).map (ι.mapTriangle.obj T).mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff _ hd i (i + 1) rfl).2 hδ
  have hz : IsZero ((DerivedCategory.homologyFunctor C i).obj (ι.mapTriangle.obj T).obj₃) := by
    rw [IsZero.iff_id_eq_zero]
    rw [← cancel_epi ((DerivedCategory.homologyFunctor C i).map (ι.mapTriangle.obj T).mor₂)]
    rw [hβ]
    simp
  exact hz

/-- **The third vertex of a distinguished triangle of `D⁺(C)` whose first morphism is invertible
on cohomology in every degree `≤ n` is bounded below by `n + 1`.** In the long exact sequence
`H^i(T₃)` is caught between an epimorphism out of `H^i(T₁)` and a monomorphism out of
`H^{i+1}(T₁)`, [Stacks, Tag 08J5]. -/
theorem isGE_three_of_isIso_homologyMap_mor₁ (T : Triangle (Plus C))
    (hT : T ∈ distTriang (Plus C)) (n : ℤ)
    (h : ∀ i : ℤ, i ≤ n + 1 → IsIso ((homologyFunctor C i).map T.mor₁)) :
    T.obj₃.IsGE (n + 1) :=
  isGE_three_of_epi_of_mono_homologyMap_mor₁ T hT n
    (fun i hi ↦ have := h i (by omega); inferInstance)
    (fun i hi ↦ have := h i hi; inferInstance)

end Triangles

section Truncation

/-- `τ_{>n}K` is bounded below by `n + 1` for the canonical t-structure of `D⁺(C)`, [Stacks,
Tag 08J5]. -/
instance isGE_truncGT_obj_succ (K : Plus C) (n : ℤ) :
    ((TStructure.t.truncGT n).obj K).IsGE (n + 1) :=
  inferInstance

/-- **The inclusion `τ_{≤n}K ⟶ K` is invertible on cohomology in every degree `≤ n`**: the third
vertex of its truncation triangle is `τ_{>n}K`, which is bounded below by `n + 1`, [Stacks,
Tag 08J5]. -/
theorem isIso_homologyMap_truncLEι_app (K : Plus C) (i n : ℤ) (hi : i ≤ n) :
    IsIso ((homologyFunctor C i).map ((TStructure.t.truncLEι n).app K)) :=
  isIso_homologyMap_mor₁_of_isGE₃ _ (TStructure.t.triangleLEGT_distinguished n K) i (n + 1)
    (inferInstanceAs (((TStructure.t.truncGT n).obj K).IsGE (n + 1))) (by omega)

/-- **The projection `K ⟶ τ_{>n}K` is invertible on cohomology in every degree `> n`**: the
first vertex of its truncation triangle is `τ_{≤n}K`, which is bounded above by `n`, [Stacks,
Tag 08J5]. -/
theorem isIso_homologyMap_truncGTπ_app (K : Plus C) (i n : ℤ) (hi : n < i) :
    IsIso ((homologyFunctor C i).map ((TStructure.t.truncGTπ n).app K)) :=
  isIso_homologyMap_mor₂_of_isLE₁ _ (TStructure.t.triangleLEGT_distinguished n K) i n
    (inferInstanceAs (((TStructure.t.truncLE n).obj K).IsLE n)) hi

/-- The cohomology of `τ_{≤n}K` vanishes in degrees `> n`, [Stacks, Tag 08J5]. -/
theorem isZero_homology_truncLE_obj (K : Plus C) (i n : ℤ) (hi : n < i) :
    IsZero ((homologyFunctor C i).obj ((TStructure.t.truncLE n).obj K)) :=
  isZero_homology_of_isLE' _ n i hi

/-- The cohomology of `τ_{>n}K` vanishes in degrees `≤ n`, [Stacks, Tag 08J5]. -/
theorem isZero_homology_truncGT_obj (K : Plus C) (i n : ℤ) (hi : i ≤ n) :
    IsZero ((homologyFunctor C i).obj ((TStructure.t.truncGT n).obj K)) :=
  isZero_homology_of_isGE' _ (n + 1) i (by omega)

end Truncation

section Single

/-- **An object of `D⁺(C)` with cohomology in a single degree is a single object there**:
if `K` is both `≥ n` and `≤ n` then it is isomorphic to `H^n(K)` placed in degree `n`, [Stacks,
Tag 0118]. -/
theorem exists_iso_singleFunctor_obj_of_isGE_of_isLE (K : Plus C) (n : ℤ)
    [K.IsGE n] [K.IsLE n] : ∃ M, Nonempty (K ≅ (singleFunctor C n).obj M) := by
  obtain ⟨M, ⟨e⟩⟩ :=
    DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE (ι.obj K) n
  exact ⟨M, ⟨ι.preimageIso (e ≪≫ ((singleFunctorιIso C n).app M).symm)⟩⟩

end Single

section Devissage

/-- Membership in `P` of an object of `C` placed in degree zero is invariant under isomorphism. -/
private theorem prop_singleFunctor_obj_of_iso (P : ObjectProperty (Plus C))
    [P.IsClosedUnderIsomorphisms] {M N : C} (e : M ≅ N) (h : P ((singleFunctor C 0).obj M)) :
    P ((singleFunctor C 0).obj N) :=
  P.prop_of_iso ((singleFunctor C 0).mapIso e) h

variable (P : ObjectProperty (Plus C)) [P.IsClosedUnderIsomorphisms]
  [P.IsStableUnderShift ℤ]

/-- **A strictly full subcategory of `D⁺(C)` stable under the shift contains an object of `C`
placed in any degree as soon as it contains it placed in degree zero**, because `M` in degree
`q` is `M` in degree zero shifted by `-q`, [Stacks, Tag 0118]. -/
theorem prop_singleFunctor_obj (M : C) (q : ℤ) (hM : P ((singleFunctor C 0).obj M)) :
    P ((singleFunctor C q).obj M) :=
  P.prop_of_iso (((singleFunctors C).shiftIso (-q) q 0 (by omega)).app M)
    (P.le_shift (-q) _ hM)

/-- An object of `D⁺(C)` whose cohomology is concentrated in the single degree `c` belongs to a
strictly full triangulated subcategory as soon as its cohomology there, placed in degree zero,
does, [Stacks, Tag 0118]. -/
theorem prop_of_isGE_of_isLE_self (K : Plus C) (c : ℤ)
    (hGE : K.IsGE c) (hLE : K.IsLE c)
    (hH : P ((singleFunctor C 0).obj ((homologyFunctor C c).obj K))) :
    P K := by
  have := hGE
  have := hLE
  obtain ⟨M, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE K c
  refine P.prop_of_iso e.symm (prop_singleFunctor_obj P M c ?_)
  exact prop_singleFunctor_obj_of_iso P
    ((homologyFunctor C c).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso c).app M) hH

variable [P.IsTriangulatedClosed₂]

omit [P.IsStableUnderShift ℤ] in
/-- The truncation triangle of the canonical t-structure of `D⁺(C)` reads membership of `K` off
membership of `τ_{≤c}K` and of `τ_{>c}K`, [Stacks, Tag 08J5]. -/
private theorem prop_of_truncLE_of_truncGT (K : Plus C) (c : ℤ)
    (hU : P ((TStructure.t.truncLE c).obj K)) (hV : P ((TStructure.t.truncGT c).obj K)) :
    P K :=
  P.ext_of_isTriangulatedClosed₂ _ (TStructure.t.triangleLEGT_distinguished c K) hU hV

/-- **The dévissage principle on `D⁺(C)`.** If `K` has no cohomology outside the window
`[a, a + n]` and each cohomology object of `K`, placed in degree zero, lies in a strictly full
triangulated subcategory `P` of `D⁺(C)`, then `K` itself lies in `P`.

The induction is on the width `n` of the window: the truncation triangle at the top of the
window splits `K` into a part with a window one shorter and a part concentrated in a single
degree, and `P` passes from two vertices of a distinguished triangle to the third, [Stacks,
Tag 08J5]. -/
theorem prop_of_isGE_of_isLE (a : ℤ) :
    ∀ (n : ℕ) (K : Plus C), K.IsGE a → K.IsLE (a + (n : ℤ)) →
      (∀ q : ℤ, a ≤ q → q ≤ a + (n : ℤ) →
        P ((singleFunctor C 0).obj ((homologyFunctor C q).obj K))) →
      P K := by
  intro n
  induction n with
  | zero =>
    intro K hGE hLE hH
    exact prop_of_isGE_of_isLE_self P K a hGE (by simpa using hLE) (hH a le_rfl (by omega))
  | succ n ih =>
    intro K hGE hLE hH
    have hcast : a + ((n + 1 : ℕ) : ℤ) = a + (n : ℤ) + 1 := by push_cast; ring
    rw [hcast] at hLE
    simp only [hcast] at hH
    have := hGE
    have := hLE
    refine prop_of_truncLE_of_truncGT P K (a + (n : ℤ)) ?_ ?_
    · refine ih _ (inferInstanceAs (((TStructure.t.truncLE (a + (n : ℤ))).obj K).IsGE a))
        (inferInstanceAs (((TStructure.t.truncLE (a + (n : ℤ))).obj K).IsLE (a + (n : ℤ))))
        fun q hq₁ hq₂ ↦ ?_
      have : IsIso ((homologyFunctor C q).map
          ((TStructure.t.truncLEι (a + (n : ℤ))).app K)) :=
        isIso_homologyMap_truncLEι_app K q (a + (n : ℤ)) hq₂
      exact prop_singleFunctor_obj_of_iso P
        (asIso ((homologyFunctor C q).map
          ((TStructure.t.truncLEι (a + (n : ℤ))).app K))).symm (hH q hq₁ (by omega))
    · refine prop_of_isGE_of_isLE_self P _ (a + (n : ℤ) + 1)
        (inferInstanceAs (((TStructure.t.truncGT (a + (n : ℤ))).obj K).IsGE (a + (n : ℤ) + 1)))
        (inferInstanceAs (((TStructure.t.truncGT (a + (n : ℤ))).obj K).IsLE (a + (n : ℤ) + 1)))
        ?_
      have hπ : IsIso ((homologyFunctor C (a + (n : ℤ) + 1)).map
          ((TStructure.t.truncGTπ (a + (n : ℤ))).app K)) :=
        isIso_homologyMap_truncGTπ_app K (a + (n : ℤ) + 1) (a + (n : ℤ)) (by omega)
      exact prop_singleFunctor_obj_of_iso P
        (asIso ((homologyFunctor C (a + (n : ℤ) + 1)).map
          ((TStructure.t.truncGTπ (a + (n : ℤ))).app K)))
        (hH (a + (n : ℤ) + 1) (by omega) (by omega))

end Devissage

end DerivedCategory.Plus
