module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Homology.PseudoCoherent.Locality

/-!
# Bounded cohomological dimension over a weak Serre subcategory

Let `C` and `D` be abelian categories, `B` a weak Serre subcategory of `C`, and
`G : D⁺(C) ⥤ D(C')` an exact functor of triangulated categories. Say that `G` has
*cohomological dimension `d` over `B`* when `G` sends every object `M[-q]` of `D⁺(C)`, for
`M ∈ B` and `q ∈ ℤ`, to an object living in cohomological degrees `≤ q + d`.

This file proves the three consequences of that hypothesis which the convergence results for
derived inverse limits on a site use. They are the local half of Stacks 0D6T: in the
Olsson--Laszlo situation of Stacks 0D6R, `G` is the right derived functor of evaluation at a
member of a distinguished covering of a basis object, and `d` is the cohomological bound
attached to that basis object. The last result of the file is the bridge that turns the
vanishing hypothesis of that situation into the cohomological-dimension hypothesis above.

## Main results

* `Stacks.BoundedCohomologicalDimension.isLE_map_obj_of_cohomology_mem`: an object of `D⁺(C)`
  with cohomology in `B` concentrated in `[a, a + n]` is sent into degrees `≤ a + n + d`.
* `Stacks.BoundedCohomologicalDimension.isZero_homology_map_obj_of_vanishing_window`: a finite
  window of vanishing cohomology kills one cohomology group of the image.
* `Stacks.BoundedCohomologicalDimension.isIso_homology_map_of_isIso_window`: a finite window of
  isomorphisms on cohomology gives an isomorphism on one cohomology group of the image.
* `Stacks.BoundedCohomologicalDimension.isLE_rightDerivedFunctorPlus_single`: a functor whose
  higher right derived functors vanish above `d` has cohomological dimension `d`.

## Implementation notes

The window `[j - d - 2, j + 1]` of the isomorphism criterion is the one of the source: two
degrees are needed above `j` to control `Hʲ` and `Hʲ⁺¹` of the cone, and `d + 2` degrees below
`j` because the bound on the image of the cone shifts by `d`.

The weak Serre subcategory is used twice and in two different strengths. The Postnikov
induction only needs `B` to be closed under isomorphism, so that is all
`isLE_map_obj_of_cohomology_mem` assumes; the cone of a map between objects with cohomology in
`B` has cohomology in `B` only because `B` cuts out a triangulated subcategory of `D(C)`
(`Stacks.DerivedCategoryB.derivedCategoryB_isTriangulated`), which needs the full
`Stacks.WeakSerre.IsWeakSerre`.

`G` is stated as a functor into the unbounded `D(C')` rather than into `D⁺(C')`, because the
conclusion is about the cohomology of the image in a fixed degree and the right derived functor
of evaluation is most easily handled after composing with the inclusion.

## References

* [Stacks Project, Tag 0D6T](https://stacks.math.columbia.edu/tag/0D6T)
* [Stacks Project, Tag 0D6R](https://stacks.math.columbia.edu/tag/0D6R)
* [Stacks Project, Tag 07K7](https://stacks.math.columbia.edu/tag/07K7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.BoundedCohomologicalDimension

/-- **An object of `D⁺` concentrated in one degree is that degree's cohomology object.**
Read through the inclusion `D⁺(C) ⥤ D(C)`, this is
`DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE`.

Used in the Postnikov induction behind Stacks 0D6T. -/
lemma exists_iso_plus_singleFunctor_obj
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory.Plus C) (q : ℤ) [K.IsGE q] [K.IsLE q] :
    ∃ M : C, Nonempty (K ≅ (DerivedCategory.Plus.singleFunctor C q).obj M) := by
  obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
    (DerivedCategory.Plus.ι.obj K) q
  exact ⟨M, ⟨DerivedCategory.Plus.ι.preimageIso
    (e ≪≫ ((DerivedCategory.Plus.singleFunctorιIso C q).app M).symm)⟩⟩

/-- The map on cohomology induced by the canonical truncation map is invertible below the
truncation degree.

Used in the truncation arguments behind Stacks 0D6T. -/
theorem isIso_plus_homologyMap_truncLEι
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory.Plus C) (a i : ℤ) (hi : i ≤ a) :
    IsIso ((DerivedCategory.Plus.homologyFunctor C i).map
      ((DerivedCategory.Plus.TStructure.t.truncLEι a).app K)) :=
  DerivedCategory.Plus.isIso_homologyMap_truncLTι_app (a + 1) i (by omega) K

/-- A property closed under isomorphisms which holds for the cohomology of `K` in degree `i ≤ a`
holds for that of `τ^{≤ a} K`. -/
private theorem prop_homology_truncLE_obj
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {B : ObjectProperty C} (hB : B.IsClosedUnderIsomorphisms)
    (K : DerivedCategory.Plus C) (a i : ℤ) (hi : i ≤ a)
    (h : B ((DerivedCategory.Plus.homologyFunctor C i).obj K)) :
    B ((DerivedCategory.Plus.homologyFunctor C i).obj
      ((DerivedCategory.Plus.TStructure.t.truncLE a).obj K)) := by
  have := isIso_plus_homologyMap_truncLEι K a i hi
  exact hB.of_iso (asIso ((DerivedCategory.Plus.homologyFunctor C i).map
    ((DerivedCategory.Plus.TStructure.t.truncLEι a).app K))).symm h

/-- **A triangulated functor of bounded cohomological dimension on a class `B` sends an object
concentrated in one degree `q` with cohomology in `B` into degrees `≤ q + d`.** -/
lemma isLE_map_obj_of_isGE_of_isLE
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    (G : DerivedCategory.Plus C ⥤ DerivedCategory D)
    (B : ObjectProperty C) (hB : B.IsClosedUnderIsomorphisms) (d : ℤ)
    (hSingle : ∀ (q : ℤ) (M : C), B M →
      (G.obj ((DerivedCategory.Plus.singleFunctor C q).obj M)).IsLE (q + d))
    (K : DerivedCategory.Plus C) (q : ℤ) [K.IsGE q] [K.IsLE q]
    (hK : B ((DerivedCategory.Plus.homologyFunctor C q).obj K)) :
    (G.obj K).IsLE (q + d) := by
  obtain ⟨M, ⟨e⟩⟩ := exists_iso_plus_singleFunctor_obj K q
  have := hSingle q M (hB.of_iso ((DerivedCategory.Plus.homologyFunctor C q).mapIso e ≪≫
    (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := C) q).app M) hK)
  exact DerivedCategory.TStructure.t.isLE_of_iso (G.mapIso e).symm (q + d)

/-- **A triangulated functor of bounded cohomological dimension on a class `B` takes a bounded
object with cohomology in `B` to an object bounded above.** If `G` sends every `M[-q]` with
`M ∈ B` to an object in cohomological degrees `≤ q + d`, then it sends every `K` in `D⁺(C)`
living in degrees `[a, a + n]` with all cohomology in `B` to an object in degrees
`≤ a + n + d`.

The proof is a finite Postnikov induction on the length `n` of the window: the top cohomology
of `K` is split off by the truncation triangle `τ^{≤ b-1}K ⟶ K ⟶ τ^{≥ b}K` with `b = a + n + 1`,
the third term is a single object of `B`, and the bound for the first term is the inductive
hypothesis.

This is the local boundedness input of Stacks 0D6T. -/
theorem isLE_map_obj_of_cohomology_mem
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    (G : DerivedCategory.Plus C ⥤ DerivedCategory D) [G.CommShift ℤ] [G.IsTriangulated]
    (B : ObjectProperty C) (hB : B.IsClosedUnderIsomorphisms) (d : ℤ)
    (hSingle : ∀ (q : ℤ) (M : C), B M →
      (G.obj ((DerivedCategory.Plus.singleFunctor C q).obj M)).IsLE (q + d)) :
    ∀ (a : ℤ) (n : ℕ) (K : DerivedCategory.Plus C), K.IsGE a → K.IsLE (a + n) →
      (∀ q : ℤ, a ≤ q → q ≤ a + n → B ((DerivedCategory.Plus.homologyFunctor C q).obj K)) →
      (G.obj K).IsLE (a + n + d) := by
  intro a n
  induction n with
  | zero =>
      intro K hGE hLE hmem
      have : K.IsLE a := by simpa using hLE
      simpa using isLE_map_obj_of_isGE_of_isLE G B hB d hSingle K a (hmem a le_rfl (by simp))
  | succ n ih =>
      intro K hGE hLE hmem
      let b := a + (n : ℤ) + 1
      have hb : b = a + n + 1 := rfl
      let t : Triangulated.TStructure (DerivedCategory.Plus C) :=
        DerivedCategory.Plus.TStructure.t
      have : K.IsLE b := by simpa [b, Nat.cast_succ, add_assoc] using hLE
      let τ := (t.truncLE (b - 1)).obj K
      let T₀ := (t.triangleLEGE (b - 1) b (sub_add_cancel b 1)).obj K
      have hT : G.mapTriangle.obj T₀ ∈ distTriang (DerivedCategory D) :=
        G.map_distinguished T₀ (t.triangleLEGE_distinguished (b - 1) b (sub_add_cancel b 1) K)
      have hτ : (G.obj τ).IsLE (a + n + d) := by
        refine ih τ ?_ (t.isLE_truncLE_obj K (b - 1) (a + n) (by omega))
          fun q haq hqb => ?_
        · dsimp [τ]
          infer_instance
        · exact prop_homology_truncLE_obj hB K (b - 1) q (by omega) (hmem q haq (by omega))
      have : T₀.obj₃.IsGE b := by
        change (t.truncGE b).obj K |>.IsGE b
        infer_instance
      have : T₀.obj₃.IsLE b := by
        change (t.truncGE b).obj K |>.IsLE b
        infer_instance
      have : IsIso ((DerivedCategory.Plus.homologyFunctor C b).map T₀.mor₂) := by
        change IsIso ((DerivedCategory.Plus.homologyFunctor C b).map ((t.truncGEπ b).app K))
        simpa [t] using DerivedCategory.Plus.isIso_homologyMap_truncGEπ_app b b le_rfl K
      have h₃ : (G.obj T₀.obj₃).IsLE (b + d) :=
        isLE_map_obj_of_isGE_of_isLE G B hB d hSingle T₀.obj₃ b
          (hB.of_iso (asIso ((DerivedCategory.Plus.homologyFunctor C b).map T₀.mor₂))
            (hmem b (by omega) (by omega)))
      have h₁ : (G.mapTriangle.obj T₀).obj₁.IsLE (b + d) := by
        change (G.obj τ).IsLE (b + d)
        exact DerivedCategory.TStructure.t.isLE_of_le _ (a + n + d) (b + d)
          (by omega)
      have hmiddle := DerivedCategory.TStructure.t.isLE₂ (G.mapTriangle.obj T₀) hT (b + d)
        h₁ (by simpa using h₃)
      change (G.obj K).IsLE (b + d) at hmiddle
      simpa [b, Nat.cast_succ, add_assoc] using hmiddle

/-- **A finite vanishing window kills one cohomology group of the image.** With `G` of
cohomological dimension `d` over the weak Serre class `B` as above, if the cohomology of `K`
vanishes in the degrees `(b, j]` and `b + d < j`, then `Hʲ(G K) = 0`.

Only the part of `K` in degrees `≤ b` can contribute to `Hʲ(G K)`: the truncation `τ^{≤ j}K`
agrees with `K` in the window, hence lives in degrees `≤ b`, so its image lives in degrees
`≤ b + d < j`; and the other truncation `τ^{≥ j+1}K` has image in degrees `≥ j + 1`.

This is the vanishing step in the local analysis of Stacks 0D6T. -/
theorem isZero_homology_map_obj_of_vanishing_window
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    (G : DerivedCategory.Plus C ⥤ DerivedCategory D) [G.CommShift ℤ] [G.IsTriangulated]
    (B : ObjectProperty C) (hB : WeakSerre.IsWeakSerre B) (d : ℤ)
    (hSingle : ∀ (q : ℤ) (M : C), B M →
      (G.obj ((DerivedCategory.Plus.singleFunctor C q).obj M)).IsLE (q + d))
    (hGE : ∀ (K : DerivedCategory.Plus C) (a : ℤ), K.IsGE a → (G.obj K).IsGE a)
    (K : DerivedCategory.Plus C) (a : ℤ) [K.IsGE a]
    (hK : ∀ q, B ((DerivedCategory.Plus.homologyFunctor C q).obj K))
    (j b : ℤ) (hb : b + d < j)
    (hwindow : ∀ q : ℤ, b < q → q ≤ j →
      IsZero ((DerivedCategory.Plus.homologyFunctor C q).obj K)) :
    IsZero ((DerivedCategory.homologyFunctor D j).obj (G.obj K)) := by
  let t := DerivedCategory.Plus.TStructure.t (C := C)
  let T := (t.triangleLEGE j (j + 1) rfl).obj K
  have hfirstGE : T.obj₁.IsGE (min a b) := by
    have := t.isGE_of_ge K (min a b) a (min_le_left _ _)
    change ((t.truncLE j).obj K).IsGE _
    infer_instance
  have hfirstLEj : T.obj₁.IsLE j := by
    change ((t.truncLE j).obj K).IsLE j
    infer_instance
  have hfirstLE : T.obj₁.IsLE b := by
    rw [← DerivedCategory.Plus.isLE_ι_obj_iff, DerivedCategory.isLE_iff]
    intro q hq
    by_cases hqj : q ≤ j
    · exact (hwindow q hq hqj).of_iso
        (@asIso _ _ _ _ ((DerivedCategory.Plus.homologyFunctor C q).map ((t.truncLEι j).app K))
          (isIso_plus_homologyMap_truncLEι K j q hqj))
    · exact DerivedCategory.Plus.isZero_homology_of_isLE T.obj₁ j q (lt_of_not_ge hqj)
  have hmem : ∀ q : ℤ, B ((DerivedCategory.Plus.homologyFunctor C q).obj T.obj₁) := by
    intro q
    by_cases hq : q ≤ j
    · exact prop_homology_truncLE_obj hB.isClosedUnderIsomorphisms K j q hq (hK q)
    · exact DerivedCategoryB.zero_mem_of_isWeakSerre B hB _
        (DerivedCategory.Plus.isZero_homology_of_isLE T.obj₁ j q (lt_of_not_ge hq))
  have hlen : min a b + ((b - min a b).toNat : ℤ) = b := by
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr (min_le_right _ _))]
    omega
  have hbound := isLE_map_obj_of_cohomology_mem G B hB.isClosedUnderIsomorphisms d hSingle
    (min a b) (b - min a b).toNat T.obj₁ hfirstGE (by simpa only [hlen] using hfirstLE)
    (fun q _ _ => hmem q)
  rw [hlen] at hbound
  have hthird : T.obj₃.IsGE (j + 1) := by
    change ((t.truncGE (j + 1)).obj K).IsGE _
    infer_instance
  have h₃GE := hGE T.obj₃ (j + 1) hthird
  exact (DerivedCategory.HomologySequence.exact₂ (G.mapTriangle.obj T)
    (G.map_distinguished T (t.triangleLEGE_distinguished j (j + 1) rfl K)) j).isZero_X₂
    (((G.obj T.obj₁).isZero_of_isLE (b + d) j hb).eq_of_src _ _)
    (((G.obj T.obj₃).isZero_of_isGE (j + 1) j (by omega)).eq_of_tgt _ _)

/-- **A finite window of isomorphisms on cohomology gives an isomorphism on the image.** With
`G` of cohomological dimension `d` over the weak Serre class `B` as above, a map `f : K ⟶ L` in
`D⁺(C)` whose induced maps on cohomology are invertible in the degrees `[j - d - 2, j + 1]`
induces an isomorphism `Hʲ(G K) ⟶ Hʲ(G L)`.

The cone of `f` has cohomology in `B` — `B` cuts out a triangulated subcategory — and vanishing
cohomology in the degrees `(j - d - 2, j]`, so the previous lemma annihilates `Hʲ⁻¹` and `Hʲ`
of its image, which is mono-ness and epi-ness of the map in question.

This is the local comparison used in the proof of Stacks 0D6T. -/
theorem isIso_homology_map_of_isIso_window
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    (G : DerivedCategory.Plus C ⥤ DerivedCategory D) [G.CommShift ℤ] [G.IsTriangulated]
    (B : ObjectProperty C) (hB : WeakSerre.IsWeakSerre B) (d : ℤ)
    (hSingle : ∀ (q : ℤ) (M : C), B M →
      (G.obj ((DerivedCategory.Plus.singleFunctor C q).obj M)).IsLE (q + d))
    (hGE : ∀ (K : DerivedCategory.Plus C) (a : ℤ), K.IsGE a → (G.obj K).IsGE a)
    {K L : DerivedCategory.Plus C}
    (hK : ∀ q, B ((DerivedCategory.Plus.homologyFunctor C q).obj K))
    (hL : ∀ q, B ((DerivedCategory.Plus.homologyFunctor C q).obj L))
    (f : K ⟶ L) (j : ℤ)
    (hwindow : ∀ q : ℤ, j - d - 2 ≤ q → q ≤ j + 1 →
      IsIso ((DerivedCategory.Plus.homologyFunctor C q).map f)) :
    IsIso ((DerivedCategory.homologyFunctor D j).map (G.map f)) := by
  obtain ⟨Z, g, δ, hT⟩ := distinguished_cocone_triangle f
  let T := Triangle.mk f g δ
  let I := DerivedCategory.Plus.ι (C := C)
  have hIT : I.mapTriangle.obj T ∈ distTriang (DerivedCategory C) :=
    I.map_distinguished T hT
  let P := DerivedCategoryB.derivedCategoryB B
  have : P.IsTriangulated := DerivedCategoryB.derivedCategoryB_isTriangulated B hB
  have : P.IsClosedUnderIsomorphisms :=
    DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms B hB
  have hZ : ∀ q, B ((DerivedCategory.Plus.homologyFunctor C q).obj Z) :=
    P.ext_of_isTriangulatedClosed₃ (I.mapTriangle.obj T) hIT hK hL
  obtain ⟨a, ha⟩ := Z.property
  have hZa : Z.IsGE a := (DerivedCategory.Plus.isGE_ι_obj_iff Z a).1 ha
  have hzero (r : ℤ) (hr : r = j - 1 ∨ r = j) :
      IsZero ((DerivedCategory.homologyFunctor D r).obj (G.obj Z)) := by
    apply isZero_homology_map_obj_of_vanishing_window G B hB d hSingle hGE Z a hZ r (j - d - 2)
    · rcases hr with rfl | rfl <;> omega
    · intro q hq hqr
      have hqj : q ≤ j := by rcases hr with rfl | rfl <;> omega
      have : IsIso ((DerivedCategory.homologyFunctor C q).map
          (I.mapTriangle.obj T).mor₁) := hwindow q (by omega) (by omega)
      have : IsIso ((DerivedCategory.homologyFunctor C (q + 1)).map
          (I.mapTriangle.obj T).mor₁) := hwindow (q + 1) (by omega) (by omega)
      exact StacksDraft.PseudoCoherence.homology_isZero_of_epi_of_mono (I.mapTriangle.obj T) hIT q
  have hGT := G.map_distinguished T hT
  have hm : Mono ((DerivedCategory.homologyFunctor D j).map (G.map f)) :=
    ((DerivedCategory.homologyFunctor D 0).homologySequence_mono_shift_map_mor₁_iff
      (G.mapTriangle.obj T) hGT (j - 1) j (by omega)).2
      ((hzero (j - 1) (Or.inl rfl)).eq_of_src _ _)
  have he : Epi ((DerivedCategory.homologyFunctor D j).map (G.map f)) :=
    ((DerivedCategory.homologyFunctor D 0).homologySequence_epi_shift_map_mor₁_iff
      (G.mapTriangle.obj T) hGT j).2 ((hzero j (Or.inr rfl)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
  Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit
  Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

/-- **A functor whose higher right derived functors vanish above `d` has cohomological
dimension `d`.** If `Rᵖ F (M) = 0` for every `p > d`, then `RF` of `M` placed in degree `q`
lives in cohomological degrees `≤ q + d`.

This is the hypothesis `hSingle` of `isLE_map_obj_of_cohomology_mem` and
`isIso_homology_map_of_isIso_window`, in the form in which the vanishing hypothesis of the
Olsson--Laszlo situation supplies it. -/
lemma isLE_rightDerivedFunctorPlus_single
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] (M : C) (d q : ℤ)
    (hvanish : ∀ p : ℕ, d < (p : ℤ) → IsZero ((F.rightDerived p).obj M)) :
    (DerivedCategory.Plus.ι.obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C q).obj M))).IsLE
        (q + d) := by
  let G := F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι
  let M₀ := (DerivedCategory.Plus.singleFunctor C 0).obj M
  have hGE : (F.rightDerivedFunctorPlus.obj M₀).IsGE 0 :=
    CategoryTheory.Functor.isGE_rightDerivedFunctorPlus_obj F M₀ 0
  have hzero : (G.obj M₀).IsLE d := by
    rw [DerivedCategory.isLE_iff]
    intro r hr
    by_cases hrneg : r < 0
    · exact DerivedCategory.Plus.isZero_homology_of_isGE
        (F.rightDerivedFunctorPlus.obj M₀) 0 r hrneg
    · have hrEq : (r.toNat : ℤ) = r := Int.toNat_of_nonneg (le_of_not_gt hrneg)
      exact (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff F hrEq.symm M).2
        (hvanish r.toNat (by omega))
  have : DerivedCategory.TStructure.t.IsLE
      ((G ⋙ shiftFunctor (DerivedCategory D) (-q)).obj M₀) (q + d) :=
    DerivedCategory.TStructure.t.isLE_shift (G.obj M₀) d (-q) (q + d) (by omega)
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (G.mapIso (((DerivedCategory.Plus.singleFunctors C).shiftIso (-q) q 0 (by omega)).app M).symm ≪≫
      (G.commShiftIso (-q)).app M₀).symm (q + d)

end Stacks.BoundedCohomologicalDimension

end
