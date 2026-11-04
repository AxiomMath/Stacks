module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Homology.Perfect.Filtration
public import StacksFrontier.Homology.Perfect.LargeUniverse

/-!
# Perfectness of `RF(K)` along the stupid filtration of a bounded complex

Let `F : 𝒜 ⥤ ℬ` be an additive functor between abelian categories with `𝒜` having enough
injectives, so that the right derived functor `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` exists and is exact
(`CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus`).  Let `K` be a cochain complex
of `𝒜` concentrated in degrees `0 ≤ i < n`.  The stupid truncations `σ^{≥ q}K` form a finite
decreasing filtration of `K` whose successive quotients are the single complexes `K^q[-q]`, and
each step is a termwise split short exact sequence, hence a distinguished triangle of `K⁺(𝒜)`
([Stacks, Tag 0118]).  Applying the exact functor `D⁺(𝒜) ⥤ D(ℬ)` term by term carries that
filtration to `D(ℬ)`.

For `ℬ` a category of modules this is the shape of
`StacksDraft.Perfect.isPerfect_of_filtration_desc`, so **`RF(K)` is perfect as soon as every
`RF(K^q[-q])` is**.  That is the statement the stupid filtration argument of the Stacks project
uses: the graded pieces are named by the *terms* of the complex and not by the object itself, so
the reduction has content (contrast the remark in
`StacksFrontier/Homology/Perfect/Filtration.lean` about one-step filtrations).

## Main definitions

Everything lives in the namespace `StacksDraft.StupidFiltration`.

* `derivedUnbounded` — the composite `K⁺(𝒜) ⥤ D⁺(𝒜) ⥤ D⁺(ℬ) ⥤ D(ℬ)`, an exact functor.
* `derivedObj`, `derivedObjNat` — `RF(K)` in `D(ℬ)`, for `K` a bounded below cochain complex of
  `𝒜` indexed by `ℤ` and by `ℕ`.
* `derivedSingle` — `RF(X[-q])` in `D(ℬ)`, for `X` an object of `𝒜`.
* `filtrationObj`, `gradedObj` — `RF(σ^{≥ q}K)` and `RF(σ^{≤ q}σ^{≥ q}K)`.

## Main results

* `isIso_ιStupidTruncGE` — a complex concentrated in degrees `≥ a` equals its own stupid
  truncation `σ^{≥ a}`.
* `stupidTruncGEIso` — `σ^{≥ b}(σ^{≥ a}K) ≅ σ^{≥ b}K` for `a ≤ b`.
* `exists_distinguished_filtration` — the image in `D(ℬ)` of the `q`-th step of the stupid
  filtration is a distinguished triangle
  `RF(σ^{≥ q+1}K) ⟶ RF(σ^{≥ q}K) ⟶ RF(σ^{≤ q}σ^{≥ q}K) ⟶ ⋯`.
* `gradedObjIsoDerivedSingle` — the `q`-th graded piece is `RF(K^q[-q])`.
* `isPerfect_derivedObj`, `isPerfect_derivedObjNat` — **`RF(K)` is perfect once every
  `RF(K^q[-q])` is**, for `K` concentrated in degrees `0 ≤ i < n`.

## References

* [Stacks Project, Tag 0118](https://stacks.math.columbia.edu/tag/0118)
* [Stacks Project, Tag 066R](https://stacks.math.columbia.edu/tag/066R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HomologicalComplex ComplexShape

universe v u

noncomputable section

namespace StacksDraft.StupidFiltration

/-! ### Two isomorphisms between stupid truncations -/

section Truncations

variable {A : Type*} [Category* A] [Abelian A]

/-- **A complex concentrated in degrees `≥ a` is its own stupid truncation `σ^{≥ a}`**: the
inclusion `σ^{≥ a}K ⟶ K` is an isomorphism, being an isomorphism in every degree `≥ a` and a map
of zero objects below `a`. -/
lemma isIso_ιStupidTruncGE (K : CochainComplex A ℤ) (a : ℤ) [K.IsStrictlyGE a] :
    IsIso (K.ιStupidTrunc (embeddingUpIntGE a)) := by
  have h (i : ℤ) : IsIso ((K.ιStupidTrunc (embeddingUpIntGE a)).f i) := by
    by_cases hi : a ≤ i
    · exact K.isIso_ιStupidTrunc_f (embeddingUpIntGE a)
        (i := (i - a).toNat) (by rw [CategoryTheory.Functor.embeddingUpIntGE_f']; omega)
    · exact IsZero.isIso (CategoryTheory.Functor.isZero_stupidTruncGE_X_of_lt K a i (by omega))
        (K.isZero_of_isStrictlyGE a i (by omega)) _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **Truncating twice on the left does nothing new**: for `a ≤ b` the stupid truncation
`σ^{≥ b}(σ^{≥ a}K)` is `σ^{≥ b}K`, the isomorphism being `σ^{≥ b}` applied to the inclusion
`σ^{≥ a}K ⟶ K`.  In degrees `≥ b` both sides are `K^i` and the map is the identity on it; below
`b` both sides vanish. -/
def stupidTruncGEIso (K : CochainComplex A ℤ) (a b : ℤ) (hab : a ≤ b) :
    (K.stupidTrunc (embeddingUpIntGE a)).stupidTrunc (embeddingUpIntGE b) ≅
      K.stupidTrunc (embeddingUpIntGE b) := by
  have h (i : ℤ) : IsIso ((stupidTruncMap (K.ιStupidTrunc (embeddingUpIntGE a))
      (embeddingUpIntGE b)).f i) := by
    by_cases hi : b ≤ i
    · have hb : (embeddingUpIntGE b).f (i - b).toNat = i := by
        rw [CategoryTheory.Functor.embeddingUpIntGE_f']; omega
      have ha : IsIso ((K.ιStupidTrunc (embeddingUpIntGE a)).f i) :=
        K.isIso_ιStupidTrunc_f (embeddingUpIntGE a)
          (i := (i - a).toNat) (by rw [CategoryTheory.Functor.embeddingUpIntGE_f']; omega)
      have key := stupidTruncMap_stupidTruncXIso_hom
        (K.ιStupidTrunc (embeddingUpIntGE a)) (embeddingUpIntGE b) hb
      have h2 : IsIso ((stupidTruncMap (K.ιStupidTrunc (embeddingUpIntGE a))
          (embeddingUpIntGE b)).f i ≫ (K.stupidTruncXIso (embeddingUpIntGE b) hb).hom) := by
        rw [key]; infer_instance
      exact IsIso.of_isIso_comp_right _ (K.stupidTruncXIso (embeddingUpIntGE b) hb).hom
    · refine IsZero.isIso ?_ ?_ _ <;>
        exact HomologicalComplex.isZero_stupidTrunc_X _ (embeddingUpIntGE b) i
          (by rw [notMem_range_embeddingUpIntGE_iff]; omega)
  have : IsIso (stupidTruncMap (K.ιStupidTrunc (embeddingUpIntGE a)) (embeddingUpIntGE b)) :=
    HomologicalComplex.Hom.isIso_of_components _
  exact asIso (stupidTruncMap (K.ιStupidTrunc (embeddingUpIntGE a)) (embeddingUpIntGE b))

end Truncations

/-! ### The image of the stupid filtration under an exact derived functor -/

section Derived

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] (F : A ⥤ B) [F.Additive] [EnoughInjectives A]

attribute [local instance] CategoryTheory.Functor.commShiftRightDerivedFunctorPlus
attribute [local instance] CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus

/-- **The right derived functor as an exact functor `K⁺(𝒜) ⥤ D(ℬ)`**: localise the bounded below
homotopy category, apply `RF`, and include `D⁺(ℬ)` into `D(ℬ)`, which is where perfectness is a
condition.  All three are exact, so this one is. -/
abbrev derivedUnbounded : HomotopyCategory.Plus A ⥤ DerivedCategory B :=
  DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι

/-- **`RF(K)` as an object of `D(ℬ)`**, for `K` a bounded below cochain complex of `𝒜`. -/
abbrev derivedObj (K : CochainComplex A ℤ) (hK : CochainComplex.plus A K) : DerivedCategory B :=
  (derivedUnbounded F).obj (CategoryTheory.Functor.plusObj K hK)

/-- **`RF(X[-q])` as an object of `D(ℬ)`**, for `X` an object of `𝒜` placed in degree `q`.  These
are the graded pieces of the stupid filtration. -/
abbrev derivedSingle (q : ℤ) (X : A) : DerivedCategory B :=
  (derivedUnbounded F).obj ((HomotopyCategory.Plus.singleFunctor A q).obj X)

/-- An isomorphism of bounded below cochain complexes induces one of the objects of `K⁺(𝒜)` they
name, the inclusion of the bounded below complexes being fully faithful. -/
def plusObjIso {K L : CochainComplex A ℤ} (hK : CochainComplex.plus A K)
    (hL : CochainComplex.plus A L) (e : K ≅ L) :
    CategoryTheory.Functor.plusObj K hK ≅ CategoryTheory.Functor.plusObj L hL :=
  (HomotopyCategory.Plus.quotient A).mapIso
    ((ObjectProperty.ι (CochainComplex.plus A)).preimageIso e)

/-- **The `q`-th step `RF(σ^{≥ q}K)` of the filtration of `RF(K)`.** -/
abbrev filtrationObj (K : CochainComplex A ℤ) (q : ℤ) : DerivedCategory B :=
  derivedObj F (K.stupidTrunc (embeddingUpIntGE q))
    (CategoryTheory.Functor.plus_stupidTruncGE K q)

/-- **The `q`-th graded piece of the filtration**, `RF` of the one-term complex
`σ^{≤ q}(σ^{≥ q}K)`.  That complex is `K^q` placed in degree `q`; see
`gradedObjIsoDerivedSingle`. -/
abbrev gradedObj (K : CochainComplex A ℤ) (q : ℤ) : DerivedCategory B :=
  (derivedUnbounded F).obj (CategoryTheory.Functor.plusTruncLE
    (K.stupidTrunc (embeddingUpIntGE q)) q (CategoryTheory.Functor.plus_stupidTruncGE K q))

/-- **The `q`-th step of the stupid filtration, read in `D(ℬ)`**: a distinguished triangle
`RF(σ^{≥ q+1}K) ⟶ RF(σ^{≥ q}K) ⟶ RF(σ^{≤ q}σ^{≥ q}K) ⟶ RF(σ^{≥ q+1}K)⟦1⟧`.

The triangle upstairs is the one attached to the termwise split short exact sequence of stupid
truncations of `σ^{≥ q}K`, [Stacks, Tag 0118]; `RF` composed with the localisation and the
inclusion of `D⁺(ℬ)` is exact, so it carries that to a distinguished triangle, and the first
vertex is moved to `RF(σ^{≥ q+1}K)` along `stupidTruncGEIso`. -/
lemma exists_distinguished_filtration (K : CochainComplex A ℤ) (q : ℤ) :
    ∃ (a : filtrationObj F K (q + 1) ⟶ filtrationObj F K q)
      (b : filtrationObj F K q ⟶ gradedObj F K q)
      (c : gradedObj F K q ⟶ (filtrationObj F K (q + 1))⟦(1 : ℤ)⟧),
      Triangle.mk a b c ∈ distTriang (DerivedCategory B) := by
  have hT := (derivedUnbounded F).map_distinguished _
    (CategoryTheory.Functor.stupidTruncTrianglehPlus_distinguished
      (K.stupidTrunc (embeddingUpIntGE q)) q (CategoryTheory.Functor.plus_stupidTruncGE K q))
  set T := (derivedUnbounded F).mapTriangle.obj
    (CategoryTheory.Functor.stupidTruncTrianglehPlus
      (K.stupidTrunc (embeddingUpIntGE q)) q (CategoryTheory.Functor.plus_stupidTruncGE K q))
    with hTdef
  have e₁ : T.obj₁ ≅ filtrationObj F K (q + 1) :=
    (derivedUnbounded F).mapIso (plusObjIso _ _ (stupidTruncGEIso K q (q + 1) (by omega)))
  refine ⟨e₁.inv ≫ T.mor₁, T.mor₂,
    T.mor₃ ≫ (shiftFunctor (DerivedCategory B) (1 : ℤ)).map e₁.hom, ?_⟩
  refine isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ e₁.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)
  · exact Category.comp_id _
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · show (T.mor₃ ≫ (shiftFunctor (DerivedCategory B) (1 : ℤ)).map e₁.hom) ≫
      (shiftFunctor (DerivedCategory B) (1 : ℤ)).map e₁.inv = 𝟙 T.obj₃ ≫ T.mor₃
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp, e₁.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

/-- **The bottom of the filtration is `RF(K)` itself**, for `K` concentrated in degrees `≥ a`:
there `σ^{≥ a}K ⟶ K` is an isomorphism of complexes. -/
def filtrationObjIsoDerivedObj (K : CochainComplex A ℤ) (hK : CochainComplex.plus A K) (a : ℤ)
    [K.IsStrictlyGE a] : filtrationObj F K a ≅ derivedObj F K hK := by
  haveI := isIso_ιStupidTruncGE K a
  exact (derivedUnbounded F).mapIso
    (plusObjIso _ hK (asIso (K.ιStupidTrunc (embeddingUpIntGE a))))

/-- **The filtration exhausts `RF(K)`**: `σ^{≥ n}K` is the zero complex as soon as `K` vanishes
in every degree `≥ n`, and an exact functor sends a zero object to a zero object. -/
lemma isZero_filtrationObj (K : CochainComplex A ℤ) (n : ℤ)
    (hn : ∀ i : ℤ, n ≤ i → IsZero (K.X i)) : IsZero (filtrationObj F K n) := by
  have h0 : IsZero (K.stupidTrunc (embeddingUpIntGE n)) := by
    rw [HomologicalComplex.isZero_stupidTrunc_iff]
    exact ⟨fun i => hn _ (by rw [CategoryTheory.Functor.embeddingUpIntGE_f']; omega)⟩
  have h1 : IsZero ((⟨K.stupidTrunc (embeddingUpIntGE n),
      CategoryTheory.Functor.plus_stupidTruncGE K n⟩ : CochainComplex.Plus A)) :=
    IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι (CochainComplex.plus A)) _ h0
  exact CategoryTheory.Functor.map_isZero _
    (CategoryTheory.Functor.map_isZero (HomotopyCategory.Plus.quotient A) h1)

/-- **The `q`-th graded piece is `RF(K^q[-q])`**: the complex `σ^{≤ q}(σ^{≥ q}K)` has `K^q` in
degree `q` and nothing elsewhere, so it is the single complex on `K^q` placed there. -/
def gradedObjIsoDerivedSingle (K : CochainComplex A ℤ) (q : ℤ) :
    gradedObj F K q ≅ derivedSingle F q (K.X q) := by
  have hq1 : (embeddingUpIntLE q).f 0 = q := by
    rw [CategoryTheory.Functor.embeddingUpIntLE_f']; omega
  have hq2 : (embeddingUpIntGE q).f 0 = q := by
    rw [CategoryTheory.Functor.embeddingUpIntGE_f']; omega
  have hzero : ∀ i : ℤ, i ≠ q →
      IsZero (((K.stupidTrunc (embeddingUpIntGE q)).stupidTrunc (embeddingUpIntLE q)).X i) := by
    intro i hi
    rcases lt_or_gt_of_ne hi with h | h
    · exact CategoryTheory.Functor.isZero_stupidTrunc_X_of_isZero _ (embeddingUpIntLE q) i
        (CategoryTheory.Functor.isZero_stupidTruncGE_X_of_lt K q i h)
    · exact CategoryTheory.Functor.isZero_stupidTruncLE_X_of_lt _ q i h
  exact (derivedUnbounded F).mapIso
    (CategoryTheory.Functor.isoSingleFunctorObjPlus _ _ q hzero ≪≫
      (HomotopyCategory.Plus.singleFunctor A q).mapIso
        (HomologicalComplex.stupidTruncXIso (K.stupidTrunc (embeddingUpIntGE q))
            (embeddingUpIntLE q) hq1 ≪≫
          HomologicalComplex.stupidTruncXIso K (embeddingUpIntGE q) hq2))

end Derived

/-! ### Perfectness of `RF(K)` -/

section Perfect

attribute [local instance] HasDerivedCategory.standard

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A] [EnoughInjectives A]
  {R : Type u} [CommRing R] (F : A ⥤ ModuleCat.{v} R) [F.Additive]

/-- **`RF(K)` is perfect once every `RF(K^q[-q])` is**, for `K` a complex of `𝒜` concentrated in
degrees `0 ≤ i < n`.

This is the stupid filtration argument: the truncations `σ^{≥ q}K` give distinguished triangles
`RF(σ^{≥ q+1}K) ⟶ RF(σ^{≥ q}K) ⟶ RF(K^q[-q]) ⟶ ⋯` of `D(R)`
(`exists_distinguished_filtration`), the filtration starts at `RF(K)` and ends at zero, and
[Stacks, Tag 066R] iterated — `StacksDraft.Perfect.isPerfect_of_filtration_desc` — turns
perfectness of the graded pieces into perfectness of `RF(K)`.

The hypothesis names the graded pieces by the *terms* of `K`, so it is not a restatement of the
conclusion; a one-step filtration would be, which is the remark in
`StacksFrontier/Homology/Perfect/Filtration.lean`. -/
theorem isPerfect_derivedObj (K : CochainComplex A ℤ) (hK : CochainComplex.plus A K)
    [K.IsStrictlyGE 0] (n : ℕ) (hn : ∀ i : ℤ, (n : ℤ) ≤ i → IsZero (K.X i))
    (hG : ∀ q : ℕ, q < n →
      StacksDraft.Perfect.IsPerfect (derivedSingle F (q : ℤ) (K.X (q : ℤ)))) :
    StacksDraft.Perfect.IsPerfect (derivedObj F K hK) := by
  refine StacksDraft.Perfect.isPerfect_of_iso (filtrationObjIsoDerivedObj F K hK 0).symm ?_
  refine StacksDraft.Perfect.isPerfect_of_filtration_desc
    (fun q => filtrationObj F K (q : ℤ)) (fun q => gradedObj F K (q : ℤ)) n
    (isZero_filtrationObj F K (n : ℤ) hn) (fun q hq =>
      StacksDraft.Perfect.isPerfect_of_iso (gradedObjIsoDerivedSingle F K (q : ℤ)) (hG q hq))
    (fun q _ => ?_)
  rw [show ((q + 1 : ℕ) : ℤ) = (q : ℤ) + 1 by push_cast; ring]
  exact exists_distinguished_filtration F K (q : ℤ)

/-- **`RF(K)` for an `ℕ`-indexed complex**, which is the form the de Rham complexes of this
library take: the complex is extended over `ℤ` by zero and read in `D(ℬ)`. -/
abbrev derivedObjNat (K : CochainComplex A ℕ) : DerivedCategory (ModuleCat.{v} R) :=
  derivedObj F (K.extend ComplexShape.embeddingUpNat) ⟨0, inferInstance⟩

/-- **`RF(K)` is perfect once every `RF(K^q[-q])` is**, for an `ℕ`-indexed complex `K` whose
terms vanish from degree `n` on.  This is `isPerfect_derivedObj` with the extension over `ℤ`
carried out: the extended complex has `K^q` in degree `q ≥ 0` and zero elsewhere. -/
theorem isPerfect_derivedObjNat (K : CochainComplex A ℕ) (n : ℕ)
    (hn : ∀ q : ℕ, n ≤ q → IsZero (K.X q))
    (hG : ∀ q : ℕ, q < n → StacksDraft.Perfect.IsPerfect (derivedSingle F (q : ℤ) (K.X q))) :
    StacksDraft.Perfect.IsPerfect (derivedObjNat F K) := by
  have hiso (q : ℕ) :
      (K.extend ComplexShape.embeddingUpNat).X (q : ℤ) ≅ K.X q :=
    K.extendXIso ComplexShape.embeddingUpNat (i := q) rfl
  refine isPerfect_derivedObj F _ _ n (fun i hi => ?_) (fun q hq => ?_)
  · have h0 : (0 : ℤ) ≤ i := le_trans (Int.natCast_nonneg n) hi
    have hx : ((i.toNat : ℕ) : ℤ) = i := Int.toNat_of_nonneg h0
    refine IsZero.of_iso (hn i.toNat ?_) ?_
    · omega
    · rw [← hx]; exact hiso i.toNat
  · exact StacksDraft.Perfect.isPerfect_of_iso
      ((derivedUnbounded F).mapIso
        ((HomotopyCategory.Plus.singleFunctor A (q : ℤ)).mapIso (hiso q))) (hG q hq)

end Perfect

end StacksDraft.StupidFiltration

end

end
