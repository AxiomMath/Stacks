module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.TotalComplexSymmetry
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.CategoryTheory.CancelIso
public import StacksCore.Algebra.Homology.TotalComplex
public import StacksCore.Algebra.Homology.TotalComplexHomotopy
public import StacksFrontier.Algebra.Homology.Embedding.StupidTrunc
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Total complexes of bounded double complexes: quasi-isomorphisms and homotopy equivalences

Let `A` be an abelian category and let `Z` be a double complex of `A` indexed by
`ℤ × ℤ` (cochain conventions in both directions) which is *bounded* in the sense that it
vanishes in negative second degrees and in first degrees `≪ 0`. This module builds the total
complex `Tot(Z)` of such a `Z` and proves the criterion of [Stacks, Tag 0133] in the form of
Weibel's acyclic assembly lemma: a morphism `f : Z ⟶ Z'` of bounded double complexes which
is a quasi-isomorphism on every column induces a quasi-isomorphism `Tot(Z) ⟶ Tot(Z')`.

## Main results

* `hasTotal_of_bounded`: a bounded double complex has a total complex, the coproducts
  defining it being finite.
* `isColimitMapCofan`: **an additive functor preserves a coproduct with finitely many nonzero
  terms**, no preservation of coproducts being assumed. This is the finiteness input to
  `HomologicalComplex₂.TotalMap.totalIsoOfFinite`.
* `quasiIso_total_map`: **[Stacks, Tag 0133]** for a morphism — a columnwise
  quasi-isomorphism of bounded double complexes is a quasi-isomorphism on total complexes.
* `totalBottomSES_shortExact`, `totalBottomSplitting`: the short exact sequence of total
  complexes obtained by deleting the bottom column of a bounded double complex, and its
  degreewise splitting.
* `totalSingleRowZeroUnit`, `isIso_totalSingleRowZeroUnit`: a cochain complex placed in
  second degree `0` has total complex the complex itself.
* `quasiIso_total_of_resolution`, `quasiIso_total_of_resolution_flip`: **[Stacks, Tag 0133]** —
  a double complex resolving a complex `K^•` column by column induces a quasi-isomorphism
  `K^• ⟶ Tot`.
* `rowZeroFunctor`: `rowZero` is a functor, with `rowZeroMap` as its action on morphisms.
* `comparisonMapP`, `quasiIso_comparisonMapP`, `comparisonHomologyIso` and
  `comparisonMapP_naturality`: **the same comparison as data rather than as an existential**, so
  that it can be natural in the resolved complex -- see the section heading for why the
  existential cannot be.
* `isHomotopyEquiv_total_of_isHomotopyEquiv`: **[Stacks, Tag 0FKH]** — a homotopy equivalence
  `M^•[0] ⟶ A^{•,•}` of complexes of complexes induces a homotopy equivalence `M^• ⟶ Tot(A^{•,•})`.

## Implementation notes

The source deduces [Stacks, Tag 0133] from the first spectral sequence of a double complex
and its convergence ([Stacks, Tag 0130], [Stacks, Tag 0132]), machinery which Mathlib does
not have. The route taken here needs none of it: it is an induction on `n - a`, where `a` is
the bound on the first degree, along the filtration of `Tot(Z)` obtained by repeatedly
deleting the bottom column.

Deleting the bottom column of `Z` is the short exact sequence of double complexes
`0 → Z^{≥ a + 1} → Z → Z^{a, •} → 0` (`bottomSES`, `bottomSES_shortExact`), whose third
term is the column `a` regarded as a double complex concentrated there (`singleColumn`) and
whose first term, the kernel of the projection `bottomProj`, is bounded with the better
bound `a + 1`. Passing to total complexes preserves short exactness here for a reason
special to this situation: in each total degree the sequence splits off the single summand
indexed by `(a, n - a)` from a coproduct with finitely many nonzero terms
(`totalBottomSplitting`, `totalBottomSES_shortExact`). Two out of three for
quasi-isomorphisms in the *middle* of a short exact sequence of complexes — which Mathlib
records as a TODO, having only the third term — is `quasiIso_τ₂`, proved from two out of
three for the distinguished triangles of the two sequences in the derived category.

Because the four lemma bounds monomorphy of the middle map in degree `n` by monomorphy of
the outer maps in degree `n` alone, while invertibility in degree `n` needs monomorphy in
degree `n + 1`, the induction runs twice: `mono_homologyMap_total_map` first, then
`epi_homologyMap_total_map`.

## References

* [Stacks, Tag 0133]
* [Stacks, Tag 012Z]
-/

@[expose] public section

open CategoryTheory Limits HomologicalComplex

namespace StacksDraft.TotalComplexQuasiIso

universe w v v' u u'

section

variable {C : Type u} [Category.{v} C] {J : Type w} {f : J → C}

/-- The restriction of a cofan to a subfamily. -/
abbrev restrictCofan (c : Cofan f) (S : Set J) : Cofan (fun j : S => f (j : J)) :=
  Cofan.mk c.pt (fun j => c.inj j.1)

open scoped Classical in
/-- **A colimit cofan restricts to a colimit cofan over any set containing the support**: the
inclusions of the terms outside the set are morphisms from a zero object, so they impose no
condition. -/
noncomputable def isColimitRestrictCofan (c : Cofan f)
    (hc : IsColimit c) (S : Set J) (hS : ∀ j, j ∉ S → IsZero (f j)) :
    IsColimit (restrictCofan c S) := by
  refine Cofan.IsColimit.mk _ (fun t => Cofan.IsColimit.desc hc (fun j =>
    if h : j ∈ S then t.inj ⟨j, h⟩ else (hS j h).to_ _)) (fun t j => ?_) (fun t m hm => ?_)
  · simp [j.2]
  · refine Cofan.IsColimit.hom_ext hc _ _ (fun j => ?_)
    by_cases h : j ∈ S
    · refine (hm ⟨j, h⟩).trans ?_
      symm
      simp [h]
    · exact (hS j h).eq_of_src _ _

/-- The converse of `isColimitRestrictCofan`: a cofan whose restriction to a set containing the
support is a colimit is itself a colimit. -/
noncomputable def isColimitOfIsColimitRestrictCofan (c : Cofan f) (S : Set J)
    (hS : ∀ j, j ∉ S → IsZero (f j)) (hc : IsColimit (restrictCofan c S)) : IsColimit c := by
  refine Cofan.IsColimit.mk _ (fun t => Cofan.IsColimit.desc hc (fun j => t.inj (j : J)))
    (fun t j => ?_) (fun t m hm => ?_)
  · by_cases h : j ∈ S
    · exact Cofan.IsColimit.fac hc (fun j : S => t.inj (j : J)) ⟨j, h⟩
    · exact (hS j h).eq_of_src _ _
  · exact Cofan.IsColimit.hom_ext hc _ _
      (fun j => (hm (j : J)).trans (Cofan.IsColimit.fac hc (fun j : S => t.inj (j : J)) j).symm)

/-- **An additive functor preserves a coproduct with finitely many nonzero terms**: it sends a
colimit cofan whose family is zero outside a finite set to a colimit cofan. No preservation of
coproducts is assumed: the restricted family is finite, so the coproduct it computes is a finite
biproduct. -/
noncomputable def isColimitMapCofan {D : Type u'} [Category.{v'} D] [Preadditive C]
    [Preadditive D] (c : Cofan f) (hc : IsColimit c) (S : Set J) [Finite S]
    (hS : ∀ j, j ∉ S → IsZero (f j)) (G : C ⥤ D) [G.Additive] :
    IsColimit (Cofan.mk (G.obj c.pt) (fun j => G.map (c.inj j))) := by
  refine isColimitOfIsColimitRestrictCofan _ S (fun j h => G.map_isZero (hS j h)) ?_
  exact Cofan.isColimitMapCoconeEquiv G _ _
    (isColimitOfPreserves G (isColimitRestrictCofan c hc S hS))

/-- **A coproduct of injective objects with finitely many nonzero terms is injective**: it is a
finite biproduct of injective objects. -/
lemma injective_cofan_pt [Preadditive C] [HasFiniteProducts C]
    (c : Cofan f) (hc : IsColimit c) (S : Set J) [Finite S] (hS : ∀ j, j ∉ S → IsZero (f j))
    (hinj : ∀ j, Injective (f j)) : Injective c.pt := by
  have : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteProducts
  have : ∀ j : S, Injective (f (j : J)) := fun j => hinj j
  have h : Injective (⨁ fun j : S => f (j : J)) := inferInstance
  exact Injective.of_iso ((isColimitRestrictCofan c hc S hS).coconePointUniqueUpToIso
    (biproduct.isColimit (fun j : S => f (j : J)))).symm h

/-- A colimit cofan all of whose terms are zero has zero vertex. -/
lemma isZero_cofan_pt [HasZeroMorphisms C] (c : Cofan f) (hc : IsColimit c)
    (hf : ∀ j, IsZero (f j)) : IsZero c.pt :=
  (IsZero.iff_id_eq_zero _).2
    (Cofan.IsColimit.hom_ext hc _ _ (fun j => (hf j).eq_of_src _ _))

end

section

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A double complex vanishing in negative second degrees and in first degrees `< a` has, in
each total degree, only finitely many nonzero terms: a nonzero `Z^{p, q}` with `p + q = n`
has `a ≤ p ≤ n`. -/
lemma finite_not_isZero_of_bounded
    (Z : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (a : ℤ)
    (hq : ∀ p q, q < 0 → IsZero ((Z.X p).X q)) (hp : ∀ p, p < a → IsZero (Z.X p)) (n : ℤ) :
    {pq : ℤ × ℤ | ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) pq = n ∧ ¬ IsZero ((Z.X pq.1).X pq.2)}.Finite := by
  refine Set.Finite.subset ((Set.finite_Icc a n).image (fun p => (p, n - p))) ?_
  rintro ⟨p, q⟩ ⟨hpq, hz⟩
  have hpq' : p + q = n := hpq
  have hq0 : 0 ≤ q := by
    by_contra h
    exact hz (hq p q (by lia))
  have hpa : a ≤ p := by
    by_contra h
    exact hz (Functor.map_isZero (HomologicalComplex.eval A (ComplexShape.up ℤ) q)
      (hp p (by lia)))
  refine ⟨p, ⟨hpa, by lia⟩, ?_⟩
  have h : n - p = q := by lia
  simp [h]

/-- The total complex of a double complex vanishing in negative second degrees and in first
degrees `≪ 0` exists: the coproducts defining it are finite. -/
lemma hasTotal_of_bounded
    (Z : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (a : ℤ)
    (hq : ∀ p q, q < 0 → IsZero ((Z.X p).X q)) (hp : ∀ p, p < a → IsZero (Z.X p)) :
    Z.HasTotal (ComplexShape.up ℤ) :=
  HomologicalComplex₂.hasTotal_of_finite _ _ (finite_not_isZero_of_bounded Z a hq hp)

/-- **The total complex of a bounded double complex of injective objects has injective terms**:
in each total degree `Tot(Z)^n` is a coproduct of the `Z^{p, q}` with `p + q = n`, all but
finitely many of which vanish, hence a finite biproduct of injective objects. -/
lemma injective_total_X_of_bounded
    (Z : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (a : ℤ)
    (hq : ∀ p q, q < 0 → IsZero ((Z.X p).X q)) (hp : ∀ p, p < a → IsZero (Z.X p))
    [Z.HasTotal (ComplexShape.up ℤ)] (hinj : ∀ p q, Injective ((Z.X p).X q)) (n : ℤ) :
    Injective ((Z.total (ComplexShape.up ℤ)).X n) := by
  let S : Set ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n}) := {i | ¬ IsZero (Z.toGradedObject i.1)}
  have : Finite ↥S :=
    (((finite_not_isZero_of_bounded Z a hq hp n).preimage Subtype.val_injective.injOn).subset
      fun i hi => ⟨i.2, hi⟩).to_subtype
  exact injective_cofan_pt _ (Z.toGradedObject.isColimitCofanMapObj _ n) S
    (fun _ hi => not_not.1 hi) (fun i => hinj i.1.1 i.1.2)

/-- The double complex concentrated in the column `p = a`, that column being the complex `W`:
the third term of the short exact sequence `0 → Z^{≥ a + 1} → Z → Z^{a, •} → 0` which deletes the
bottom column of a double complex vanishing in first degrees `< a`. -/
noncomputable abbrev singleColumn (W : CochainComplex A ℤ) (a : ℤ) :
    HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (HomologicalComplex.single (CochainComplex A ℤ) (ComplexShape.up ℤ) a).obj W

/-- Outside the column `a`, every object of `singleColumn W a` is zero. -/
lemma isZero_singleColumn_X_X (W : CochainComplex A ℤ) (a p : ℤ) (hp : p ≠ a) (q : ℤ) :
    IsZero (((singleColumn W a).X p).X q) :=
  Functor.map_isZero (HomologicalComplex.eval A (ComplexShape.up ℤ) q)
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a W p hp)

/-- A double complex concentrated in one column has, in each total degree, exactly one possibly
nonzero term. -/
lemma finite_not_isZero_singleColumn (W : CochainComplex A ℤ) (a n : ℤ) :
    {pq : ℤ × ℤ | ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) pq = n ∧ ¬ IsZero (((singleColumn W a).X pq.1).X pq.2)}.Finite := by
  refine Set.Finite.subset (Set.finite_singleton (a, n - a)) ?_
  rintro ⟨p, q⟩ ⟨hpq, hz⟩
  have hpq' : p + q = n := hpq
  by_cases hp : p = a
  · have hq : q = n - a := by lia
    simp [hp, hq]
  · exact absurd (isZero_singleColumn_X_X W a p hp q) hz

/-- The total complex of a double complex concentrated in one column exists. -/
lemma hasTotal_singleColumn (W : CochainComplex A ℤ) (a : ℤ) :
    (singleColumn W a).HasTotal (ComplexShape.up ℤ) :=
  HomologicalComplex₂.hasTotal_of_finite _ _ (finite_not_isZero_singleColumn W a)

/-- **The projection of a double complex onto its bottom column**, `Z ⟶ Z^{a, •}` viewed as a
double complex concentrated in the column `a`. It is defined as soon as the column `a - 1`
vanishes, for then no differential enters the column `a`, and its kernel is the stupid truncation
`Z^{≥ a + 1}`. -/
noncomputable def bottomProj
    (Z : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (a : ℤ)
    (hZ : IsZero (Z.X (a - 1))) : Z ⟶ singleColumn (Z.X a) a :=
  HomologicalComplex.mkHomToSingle (𝟙 (Z.X a)) (fun i hi => by
    obtain rfl : i = a - 1 := by
      have hi' : i + 1 = a := hi
      lia
    rw [Category.comp_id]
    exact hZ.eq_of_src _ _)

/-- **Two out of three for quasi-isomorphisms, in the middle**: a morphism of short exact
sequences of cochain complexes which is a quasi-isomorphism on the outer terms is one in the
middle. Mathlib has this for the third term (`HomologicalComplex.HomologySequence.quasiIso_τ₃`)
and records the other two as a TODO; the proof here is not the five lemma but two out of three
for the distinguished triangles of the two sequences in the derived category. -/
lemma quasiIso_τ₂ {S₁ S₂ : ShortComplex (CochainComplex A ℤ)} (φ : S₁ ⟶ S₂)
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) [QuasiIso φ.τ₁] [QuasiIso φ.τ₃] :
    QuasiIso φ.τ₂ := by
  let _i := HasDerivedCategory.standard A
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact Pretriangulated.isIso₂_of_isIso₁₃ (DerivedCategory.triangleOfSES.map h₁ h₂ φ)
    (DerivedCategory.triangleOfSES_distinguished h₁)
    (DerivedCategory.triangleOfSES_distinguished h₂)
    ((DerivedCategory.isIso_Q_map_iff_quasiIso (φ := φ.τ₁)).2 inferInstance)
    ((DerivedCategory.isIso_Q_map_iff_quasiIso (φ := φ.τ₃)).2 inferInstance)

/-- The inclusion of a summand of a total complex is unchanged, up to the identification of the
terms, when the second index is replaced by an equal one. -/
lemma ιTotal_congr₂ (Z : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [Z.HasTotal (ComplexShape.up ℤ)] (p q q' n : ℤ) (h : q = q')
    (hq : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    Z.ιTotal (ComplexShape.up ℤ) p q n hq =
      ((Z.X p).XIsoOfEq h).hom ≫ Z.ιTotal (ComplexShape.up ℤ) p q' n (by subst h; exact hq) := by
  subst h
  simp

/-- **The total complex vanishes below the bound**: every summand `Z^{p, q}` of `Tot(Z)^n` has
either `q < 0` or `p < a`. -/
lemma isZero_total_X
    (Z : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (a : ℤ)
    (hq : ∀ p q, q < 0 → IsZero ((Z.X p).X q)) (hp : ∀ p, p < a → IsZero (Z.X p))
    [Z.HasTotal (ComplexShape.up ℤ)] (n : ℤ) (hn : n < a) :
    IsZero ((Z.total (ComplexShape.up ℤ)).X n) := by
  refine isZero_cofan_pt _ (Z.toGradedObject.isColimitCofanMapObj _ n) (fun i => ?_)
  obtain ⟨⟨p, q⟩, hpq⟩ := i
  have hpq' : p + q = n := hpq
  by_cases h : a ≤ p
  · exact hq p q (by lia)
  · exact Functor.map_isZero (HomologicalComplex.eval A (ComplexShape.up ℤ) q) (hp p (by lia))

/-- A complex which vanishes in degree `n` has no homology there. -/
lemma isZero_homology_of_isZero_X {K : CochainComplex A ℤ} (n : ℤ) (h : IsZero (K.X n)) :
    IsZero (K.homology n) :=
  IsZero.of_epi (homologyπ K n) (IsZero.of_mono (iCycles K n) h)

/-- A morphism between zero objects is an isomorphism. -/
lemma isIso_of_isZero {X Y : A} (g : X ⟶ Y) (hX : IsZero X) (hY : IsZero Y) : IsIso g :=
  ⟨0, hX.eq_of_src _ _, hY.eq_of_src _ _⟩

section SingleColumn

variable (W : CochainComplex A ℤ) (a : ℤ) [(singleColumn W a).HasTotal (ComplexShape.up ℤ)]

/-- The projection of `Tot(W[a])^n` onto its only possibly nonzero summand, the one indexed by
`(a, n - a)`, followed by the identification of that summand with `W^{n - a}`. -/
noncomputable def totalSingleColumnDesc (n : ℤ) :
    ((singleColumn W a).total (ComplexShape.up ℤ)).X n ⟶
      ((CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-a)).obj W).X n :=
  (singleColumn W a).totalDesc (fun p q h =>
    if hp : p = a then
      eqToHom (by
        have h' : p + q = n := h
        subst hp
        rw [show q = n + -p from by lia]) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a W).hom.f (n + -a)
    else (isZero_singleColumn_X_X W a p hp q).to_ _)

/-- On the summand indexed by `(a, n - a)`, `totalSingleColumnDesc` is the identification of
that summand with `W^{n - a}`. -/
@[reassoc]
lemma ι_totalSingleColumnDesc (n : ℤ) :
    (singleColumn W a).ιTotal (ComplexShape.up ℤ) a (n + -a) n (by dsimp; lia) ≫
        totalSingleColumnDesc W a n =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a W).hom.f (n + -a) := by
  rw [totalSingleColumnDesc, HomologicalComplex₂.ι_totalDesc]
  simp

/-- **The total complex of a double complex concentrated in the column `a` is the shift by `-a`
of that column**: `Tot(W[a])^n` is the single summand `W^{n - a}`, and by [Stacks, Tag 012Z] its
differential is `(-1)^a d_W`, which is the differential of `W⟦-a⟧` because
`(-a).negOnePow = (-1)^a`. This is the morphism `W⟦-a⟧ ⟶ Tot(W[a])`; it is an isomorphism. -/
noncomputable def totalSingleColumnUnit :
    (CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-a)).obj W ⟶
      (singleColumn W a).total (ComplexShape.up ℤ) where
  f n := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a W).inv.f (n + -a) ≫
    (singleColumn W a).ιTotal (ComplexShape.up ℤ) a (n + -a) n (by dsimp; lia)
  comm' n n' h := by
    obtain rfl : n + 1 = n' := h
    have hd1 : (singleColumn W a).d a (a + 1) = 0 :=
      HomologicalComplex.single_obj_d _ _ _ _ _
    have he : n + -a + 1 = n + 1 + -a := by lia
    dsimp
    rw [Category.assoc, HomologicalComplex₂.ιTotal_d_up_ℤ _ a (n + -a) n (by lia), hd1]
    simp only [HomologicalComplex.zero_f, zero_comp, zero_add, Int.negOnePow_neg, Units.smul_def,
      Preadditive.comp_zsmul, Preadditive.zsmul_comp]
    rw [ιTotal_congr₂ (singleColumn W a) a (n + -a + 1) (n + 1 + -a) (n + 1) he (by dsimp; lia)]
    congr 1
    rw [reassoc_of% (HomologicalComplex.d_comp_XIsoOfEq_hom ((singleColumn W a).X a) he (n + -a)),
      reassoc_of% (HomologicalComplex.Hom.comm
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a W).inv (n + -a) (n + 1 + -a))]

/-- Each component of `totalSingleColumnUnit W a` is an isomorphism, with inverse
`totalSingleColumnDesc W a n`. -/
lemma isIso_totalSingleColumnUnit_f (n : ℤ) :
    IsIso ((totalSingleColumnUnit W a).f n) := by
  refine ⟨totalSingleColumnDesc W a n, ?_, ?_⟩
  · dsimp [totalSingleColumnUnit]
    rw [Category.assoc, ι_totalSingleColumnDesc]
    simp
  · refine HomologicalComplex₂.total.hom_ext (ComplexShape.up ℤ) (fun p q h => ?_)
    by_cases hp : p = a
    · have h' : p + q = n := h
      subst hp
      obtain rfl : q = n + -p := by lia
      rw [Category.comp_id, ← Category.assoc, ι_totalSingleColumnDesc]
      dsimp [totalSingleColumnUnit]
      simp
    · exact (isZero_singleColumn_X_X W a p hp q).eq_of_src _ _

/-- The morphism `W⟦-a⟧ ⟶ Tot(W[a])` is an isomorphism of cochain complexes. -/
lemma isIso_totalSingleColumnUnit : IsIso (totalSingleColumnUnit W a) := by
  have := isIso_totalSingleColumnUnit_f W a
  exact HomologicalComplex.Hom.isIso_of_components _

end SingleColumn

/-- `W ↦ Tot(W[a])` and `W ↦ W⟦-a⟧` are identified naturally in `W`. -/
lemma totalSingleColumnUnit_naturality {W W' : CochainComplex A ℤ} (g : W ⟶ W') (a : ℤ)
    [(singleColumn W a).HasTotal (ComplexShape.up ℤ)]
    [(singleColumn W' a).HasTotal (ComplexShape.up ℤ)] :
    (CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-a)).map g ≫ totalSingleColumnUnit W' a =
      totalSingleColumnUnit W a ≫
        HomologicalComplex₂.total.map ((HomologicalComplex.single (CochainComplex A ℤ)
          (ComplexShape.up ℤ) a).map g) (ComplexShape.up ℤ) := by
  ext n
  have hio : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a W).inv.f (n + -a) ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a W).hom.f (n + -a) = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  dsimp [totalSingleColumnUnit]
  rw [Category.assoc, HomologicalComplex₂.ιTotal_map]
  simp only [HomologicalComplex.single_map_f_self, HomologicalComplex.comp_f, Category.assoc,
    reassoc_of% hio]

/-- **A quasi-isomorphism of complexes stays one after placing it in the column `a` and taking
total complexes**: both total complexes are the shift by `-a` of the columns, naturally. -/
lemma quasiIso_total_map_singleColumn {W W' : CochainComplex A ℤ} (g : W ⟶ W') (a : ℤ)
    [(singleColumn W a).HasTotal (ComplexShape.up ℤ)]
    [(singleColumn W' a).HasTotal (ComplexShape.up ℤ)] [QuasiIso g] :
    QuasiIso (HomologicalComplex₂.total.map ((HomologicalComplex.single (CochainComplex A ℤ)
      (ComplexShape.up ℤ) a).map g) (ComplexShape.up ℤ)) := by
  have h₁ := isIso_totalSingleColumnUnit W a
  have h₂ := isIso_totalSingleColumnUnit W' a
  have key : HomologicalComplex₂.total.map ((HomologicalComplex.single (CochainComplex A ℤ)
      (ComplexShape.up ℤ) a).map g) (ComplexShape.up ℤ) =
        inv (totalSingleColumnUnit W a) ≫
          ((CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-a)).map g ≫
            totalSingleColumnUnit W' a) := by
    rw [totalSingleColumnUnit_naturality, IsIso.inv_hom_id_assoc]
  rw [key]
  infer_instance

/-- **A kernel of a morphism whose target is a zero object is an isomorphism**: the identity
factors through it, so it is a split epi, and it is a mono. -/
lemma isIso_of_isLimit_kernelFork_of_isZero {C : Type*} [Category C] [Abelian C]
    {X Y K : C} {i : K ⟶ X} {g : X ⟶ Y} (w : i ≫ g = 0)
    (h : IsLimit (KernelFork.ofι i w)) (hY : IsZero Y) : IsIso i := by
  have hm : Mono i := mono_of_isLimit_fork h
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' h (𝟙 X) (hY.eq_of_tgt _ _)
  have : IsSplitEpi i := ⟨⟨⟨l, hl⟩⟩⟩
  exact isIso_of_mono_of_epi i

section BottomTrunc

variable (Z : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (a : ℤ)
  (hZ : IsZero (Z.X (a - 1)))

/-- In the column `a` the projection onto the bottom column is the canonical identification. -/
lemma bottomProj_f_self : (bottomProj Z a hZ).f a =
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a (Z.X a)).inv := by
  rw [bottomProj, HomologicalComplex.mkHomToSingle_f, Category.id_comp]

/-- Outside the column `a` the projection onto the bottom column vanishes. -/
lemma bottomProj_f_of_ne (p : ℤ) (hp : p ≠ a) : (bottomProj Z a hZ).f p = 0 :=
  (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a (Z.X a) p hp).eq_of_tgt _ _

/-- The projection onto the bottom column is an epimorphism: in the column `a` it is an
isomorphism, and elsewhere its target vanishes. -/
lemma epi_bottomProj : Epi (bottomProj Z a hZ) :=
  HomologicalComplex.epi_of_epi_f _ (fun p => by
    by_cases hp : p = a
    · subst hp
      rw [bottomProj_f_self]
      infer_instance
    · exact ⟨fun _ _ _ => (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a
        (Z.X a) p hp).eq_of_src _ _⟩)

/-- **The stupid truncation `Z^{≥ a + 1}`**, the short exact sequence
`0 → Z^{≥ a + 1} → Z → Z^{a, •} → 0` which deletes the bottom column of a double complex
vanishing in first degrees `< a`. The truncation is taken as the kernel of `bottomProj`, so that
its inclusion, and the morphism it induces from a morphism of double complexes, are the ones
`kernel.ι` and `kernel.map` provide. -/
noncomputable def bottomSES :
    ShortComplex (HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)) :=
  ShortComplex.mk (kernel.ι (bottomProj Z a hZ)) (bottomProj Z a hZ) (kernel.condition _)

/-- The sequence `0 → Z^{≥ a + 1} → Z → Z^{a, •} → 0` is short exact. -/
lemma bottomSES_shortExact : (bottomSES Z a hZ).ShortExact where
  mono_f := by dsimp only [bottomSES]; infer_instance
  epi_g := by dsimp only [bottomSES]; exact epi_bottomProj Z a hZ
  exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)

/-- Outside the column `a` the truncation agrees with `Z`. -/
lemma isIso_kernel_ι_bottomProj_f (p : ℤ) (hp : p ≠ a) :
    IsIso ((kernel.ι (bottomProj Z a hZ)).f p) :=
  isIso_of_isLimit_kernelFork_of_isZero _
    (isLimitForkMapOfIsLimit' (HomologicalComplex.eval (CochainComplex A ℤ) (ComplexShape.up ℤ) p)
      (kernel.condition (bottomProj Z a hZ)) (kernelIsKernel (bottomProj Z a hZ)))
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a (Z.X a) p hp)

/-- In the column `a` the truncation vanishes: there the inclusion is a mono whose composition
with the isomorphism `(bottomProj Z a hZ).f a` is zero. -/
lemma isZero_kernel_bottomProj_X_self : IsZero ((kernel (bottomProj Z a hZ)).X a) := by
  have h0 : (kernel.ι (bottomProj Z a hZ)).f a = 0 := by
    have hiso : IsIso ((bottomProj Z a hZ).f a) := by rw [bottomProj_f_self]; infer_instance
    refine zero_of_comp_mono ((bottomProj Z a hZ).f a) ?_
    rw [← HomologicalComplex.comp_f, kernel.condition, HomologicalComplex.zero_f]
  refine (IsZero.iff_id_eq_zero _).2 ?_
  rwa [← cancel_mono ((kernel.ι (bottomProj Z a hZ)).f a), Category.id_comp, zero_comp]

/-- The truncation `Z^{≥ a + 1}` vanishes in every first degree in which `Z` vanishes. -/
lemma isZero_kernel_bottomProj_X (p : ℤ) (h : IsZero (Z.X p)) :
    IsZero ((kernel (bottomProj Z a hZ)).X p) :=
  IsZero.of_mono ((kernel.ι (bottomProj Z a hZ)).f p) h

/-- The truncation `Z^{≥ a + 1}` vanishes in every bidegree in which `Z` vanishes. -/
lemma isZero_kernel_bottomProj_X_X (p q : ℤ) (h : IsZero ((Z.X p).X q)) :
    IsZero (((kernel (bottomProj Z a hZ)).X p).X q) :=
  IsZero.of_mono (((kernel.ι (bottomProj Z a hZ)).f p).f q) h

/-- **The truncation satisfies the hypotheses of the acyclic assembly lemma with the bound
`a + 1`**, so that its total complex exists. -/
lemma hasTotal_kernel_bottomProj (hq : ∀ p q, q < 0 → IsZero ((Z.X p).X q))
    (hp : ∀ p, p < a → IsZero (Z.X p)) :
    (kernel (bottomProj Z a hZ)).HasTotal (ComplexShape.up ℤ) :=
  hasTotal_of_bounded _ (a + 1)
    (fun p q hq' => isZero_kernel_bottomProj_X_X Z a hZ p q (hq p q hq'))
    (fun p hp' => by
      by_cases h : p = a
      · rw [h]
        exact isZero_kernel_bottomProj_X_self Z a hZ
      · exact isZero_kernel_bottomProj_X Z a hZ p (hp p (by lia)))

end BottomTrunc

section BottomTotal

variable (Z : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (a : ℤ)
  (hZ : IsZero (Z.X (a - 1))) [Z.HasTotal (ComplexShape.up ℤ)]
  [(kernel (bottomProj Z a hZ)).HasTotal (ComplexShape.up ℤ)]
  [(singleColumn (Z.X a) a).HasTotal (ComplexShape.up ℤ)]

/-- **The short complex of total complexes** obtained by applying `Tot` to the short exact
sequence `0 → Z^{≥ a + 1} → Z → Z^{a, •} → 0` of `bottomSES`. -/
noncomputable def totalBottomSES : ShortComplex (CochainComplex A ℤ) :=
  ShortComplex.mk
    (HomologicalComplex₂.total.map (kernel.ι (bottomProj Z a hZ)) (ComplexShape.up ℤ))
    (HomologicalComplex₂.total.map (bottomProj Z a hZ) (ComplexShape.up ℤ))
    (by rw [← HomologicalComplex₂.total.map_comp, kernel.condition,
      HomologicalComplex₂.total.map_zero])

omit [Z.HasTotal (ComplexShape.up ℤ)] [(kernel (bottomProj Z a hZ)).HasTotal (ComplexShape.up ℤ)]
  [(singleColumn (Z.X a) a).HasTotal (ComplexShape.up ℤ)] in
/-- Off the column `a` the inclusion of the truncation is an isomorphism in each bidegree. -/
lemma isIso_kernel_ι_bottomProj_f_f (p : ℤ) (hp : p ≠ a) (q : ℤ) :
    IsIso (((kernel.ι (bottomProj Z a hZ)).f p).f q) :=
  have _ := isIso_kernel_ι_bottomProj_f Z a hZ p hp
  inferInstance

/-- The retraction, in total degree `n`, of `Tot(Z^{≥ a + 1})^n ⟶ Tot(Z)^n`: on the summand
indexed by `(p, q)` with `p ≠ a` it is the inverse of `isIso_kernel_ι_bottomProj_f`, and it is
zero on the single summand lying in the column `a`. -/
noncomputable def totalBottomRetraction (n : ℤ) :
    (Z.total (ComplexShape.up ℤ)).X n ⟶
      ((kernel (bottomProj Z a hZ)).total (ComplexShape.up ℤ)).X n :=
  Z.totalDesc (fun p q h =>
    if hp : p = a then 0
    else
      have _ := isIso_kernel_ι_bottomProj_f_f Z a hZ p hp q
      inv (((kernel.ι (bottomProj Z a hZ)).f p).f q) ≫
        (kernel (bottomProj Z a hZ)).ιTotal (ComplexShape.up ℤ) p q n h)

omit [(singleColumn (Z.X a) a).HasTotal (ComplexShape.up ℤ)] in
/-- On the summand indexed by `(p, q)` with `p ≠ a`, `totalBottomRetraction` is the inverse of
the inclusion of the truncation followed by the inclusion of that summand. -/
@[reassoc]
lemma ι_totalBottomRetraction_of_ne (n p q : ℤ) (hp : p ≠ a)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n)
    [IsIso (((kernel.ι (bottomProj Z a hZ)).f p).f q)] :
    Z.ιTotal (ComplexShape.up ℤ) p q n h ≫ totalBottomRetraction Z a hZ n =
      inv (((kernel.ι (bottomProj Z a hZ)).f p).f q) ≫
        (kernel (bottomProj Z a hZ)).ιTotal (ComplexShape.up ℤ) p q n h := by
  rw [totalBottomRetraction, HomologicalComplex₂.ι_totalDesc, dite_eq_right hp]

omit [(singleColumn (Z.X a) a).HasTotal (ComplexShape.up ℤ)] in
/-- On the summand indexed by `(a, q)`, `totalBottomRetraction` is zero. -/
@[reassoc]
lemma ι_totalBottomRetraction_self (n q : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, q) = n) :
    Z.ιTotal (ComplexShape.up ℤ) a q n h ≫ totalBottomRetraction Z a hZ n = 0 := by
  rw [totalBottomRetraction, HomologicalComplex₂.ι_totalDesc, dite_eq_left rfl]

/-- The retraction and the section add up to the identity of `Tot(Z)^n`: on the summand in the
column `a` the retraction vanishes and the section is inverse to the projection, and on every
other summand the projection vanishes and the retraction is inverse to the inclusion. -/
lemma totalBottom_id (n : ℤ) :
    totalBottomRetraction Z a hZ n ≫
        (HomologicalComplex₂.total.map (kernel.ι (bottomProj Z a hZ)) (ComplexShape.up ℤ)).f n +
      (HomologicalComplex₂.total.map (bottomProj Z a hZ) (ComplexShape.up ℤ)).f n ≫
        (totalSingleColumnDesc (Z.X a) a n ≫
          Z.ιTotal (ComplexShape.up ℤ) a (n + -a) n (by dsimp; lia)) =
      𝟙 ((Z.total (ComplexShape.up ℤ)).X n) := by
  refine HomologicalComplex₂.total.hom_ext (ComplexShape.up ℤ) (fun p q h => ?_)
  rw [Category.comp_id, Preadditive.comp_add]
  by_cases hp : p = a
  · subst hp
    have h' : p + q = n := h
    obtain rfl : q = n + -p := by lia
    simp only [ι_totalBottomRetraction_self_assoc Z p hZ n (n + -p) h, zero_comp, zero_add,
      HomologicalComplex₂.ιTotal_map_assoc, bottomProj_f_self, ι_totalSingleColumnDesc_assoc]
    rw [← Category.assoc, ← HomologicalComplex.comp_f, Iso.inv_hom_id,
      HomologicalComplex.id_f, Category.id_comp]
  · have _ := isIso_kernel_ι_bottomProj_f_f Z a hZ p hp q
    simp only [HomologicalComplex₂.ιTotal_map_assoc, bottomProj_f_of_ne Z a hZ p hp,
      HomologicalComplex.zero_f, zero_comp, add_zero,
      ι_totalBottomRetraction_of_ne_assoc Z a hZ n p q hp h, HomologicalComplex₂.ιTotal_map,
      IsIso.inv_hom_id_assoc]

/-- **In each total degree the short complex of total complexes is split**: it is the splitting
off of the single summand indexed by `(a, n - a)` from a coproduct. -/
noncomputable def totalBottomSplitting (n : ℤ) :
    ((totalBottomSES Z a hZ).map (HomologicalComplex.eval A (ComplexShape.up ℤ) n)).Splitting where
  r := totalBottomRetraction Z a hZ n
  s := totalSingleColumnDesc (Z.X a) a n ≫
    Z.ιTotal (ComplexShape.up ℤ) a (n + -a) n (by dsimp; lia)
  f_r := by
    dsimp only [totalBottomSES, ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_f,
      HomologicalComplex.eval_obj, HomologicalComplex.eval_map]
    refine HomologicalComplex₂.total.hom_ext (ComplexShape.up ℤ) (fun p q h => ?_)
    by_cases hp : p = a
    · refine (?_ : IsZero (((kernel (bottomProj Z a hZ)).X p).X q)).eq_of_src _ _
      rw [hp]
      exact Functor.map_isZero (HomologicalComplex.eval A (ComplexShape.up ℤ) q)
        (isZero_kernel_bottomProj_X_self Z a hZ)
    · have _ := isIso_kernel_ι_bottomProj_f_f Z a hZ p hp q
      simp only [Category.comp_id, HomologicalComplex₂.ιTotal_map_assoc,
        ι_totalBottomRetraction_of_ne Z a hZ n p q hp h, IsIso.hom_inv_id_assoc]
  s_g := by
    dsimp only [totalBottomSES, ShortComplex.map_X₃, ShortComplex.map_g,
      HomologicalComplex.eval_obj, HomologicalComplex.eval_map]
    refine HomologicalComplex₂.total.hom_ext (ComplexShape.up ℤ) (fun p q h => ?_)
    by_cases hp : p = a
    · subst hp
      have h' : p + q = n := h
      obtain rfl : q = n + -p := by lia
      simp only [Category.assoc, Category.comp_id, ι_totalSingleColumnDesc_assoc,
        HomologicalComplex₂.ιTotal_map, bottomProj_f_self]
      rw [← Category.assoc, ← HomologicalComplex.comp_f, Iso.hom_inv_id,
        HomologicalComplex.id_f, Category.id_comp]
    · exact (isZero_singleColumn_X_X (Z.X a) a p hp q).eq_of_src _ _
  id := totalBottom_id Z a hZ n

/-- **The total complexes of `bottomSES` form a short exact sequence.** In total degree `n` it is
the splitting off of a single summand from a coproduct, `totalBottomSplitting`. -/
lemma totalBottomSES_shortExact : (totalBottomSES Z a hZ).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => (totalBottomSplitting Z a hZ n).shortExact)

end BottomTotal

section BottomMap

/-- A morphism between two zero objects is an isomorphism. -/
lemma isIso_of_isZero_of_isZero {C : Type*} [Category C] [HasZeroMorphisms C] {X Y : C}
    (g : X ⟶ Y) (hX : IsZero X) (hY : IsZero Y) : IsIso g :=
  ⟨0, hX.eq_of_src _ _, hY.eq_of_src _ _⟩

/-- **The projection onto the bottom column is natural**: in the column `a` both projections are
the canonical identification of the column with itself viewed in a single-column double complex,
and outside that column the target vanishes. -/
lemma bottomProj_naturality
    {Z Z' : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)} (f : Z ⟶ Z') (a : ℤ)
    (hZ : IsZero (Z.X (a - 1))) (hZ' : IsZero (Z'.X (a - 1))) :
    bottomProj Z a hZ ≫
        (HomologicalComplex.single (CochainComplex A ℤ) (ComplexShape.up ℤ) a).map (f.f a) =
      f ≫ bottomProj Z' a hZ' :=
  HomologicalComplex.to_single_hom_ext (by
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, bottomProj_f_self,
      HomologicalComplex.single_map_f_self, bottomProj_f_self, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp])

/-- **The morphism induced on the stupid truncations** `Z^{≥ a + 1} ⟶ Z'^{≥ a + 1}`, obtained
from the naturality square of `bottomProj` by `kernel.map`. -/
noncomputable abbrev bottomTruncMap
    {Z Z' : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)} (f : Z ⟶ Z') (a : ℤ)
    (hZ : IsZero (Z.X (a - 1))) (hZ' : IsZero (Z'.X (a - 1))) :
    kernel (bottomProj Z a hZ) ⟶ kernel (bottomProj Z' a hZ') :=
  kernel.map _ _ f _ (bottomProj_naturality f a hZ hZ')

/-- `bottomTruncMap f a hZ hZ'` commutes with the inclusions of the truncations and with `f`. -/
@[reassoc]
lemma bottomTruncMap_ι
    {Z Z' : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)} (f : Z ⟶ Z') (a : ℤ)
    (hZ : IsZero (Z.X (a - 1))) (hZ' : IsZero (Z'.X (a - 1))) :
    bottomTruncMap f a hZ hZ' ≫ kernel.ι (bottomProj Z' a hZ') =
      kernel.ι (bottomProj Z a hZ) ≫ f :=
  kernel.lift_ι _ _ _

/-- **The truncation map is a quasi-isomorphism on each column**: outside the column `a` it is
conjugate to `f` by the isomorphisms `isIso_kernel_ι_bottomProj_f`, and in the column `a` both
truncations vanish. -/
lemma quasiIso_bottomTruncMap_f
    {Z Z' : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)} (f : Z ⟶ Z') (a : ℤ)
    (hZ : IsZero (Z.X (a - 1))) (hZ' : IsZero (Z'.X (a - 1))) (hf : ∀ p, QuasiIso (f.f p))
    (p : ℤ) :
    QuasiIso ((bottomTruncMap f a hZ hZ').f p) := by
  by_cases hp : p = a
  · have hz : IsZero ((kernel (bottomProj Z a hZ)).X p) := by
      rw [hp]; exact isZero_kernel_bottomProj_X_self Z a hZ
    have hz' : IsZero ((kernel (bottomProj Z' a hZ')).X p) := by
      rw [hp]; exact isZero_kernel_bottomProj_X_self Z' a hZ'
    have := isIso_of_isZero_of_isZero ((bottomTruncMap f a hZ hZ').f p) hz hz'
    infer_instance
  · have h₁ := isIso_kernel_ι_bottomProj_f Z a hZ p hp
    have h₂ := isIso_kernel_ι_bottomProj_f Z' a hZ' p hp
    have hcomp : (bottomTruncMap f a hZ hZ').f p ≫ (kernel.ι (bottomProj Z' a hZ')).f p =
        (kernel.ι (bottomProj Z a hZ)).f p ≫ f.f p := by
      rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, bottomTruncMap_ι]
    have key : (bottomTruncMap f a hZ hZ').f p =
        (kernel.ι (bottomProj Z a hZ)).f p ≫
          f.f p ≫ inv ((kernel.ι (bottomProj Z' a hZ')).f p) := by
      rw [← Category.assoc, ← hcomp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [key]
    have := hf p
    infer_instance

/-- The stupid truncation still vanishes in negative second degrees. -/
lemma isZero_bottomTrunc_X_X
    {Z : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)} (a : ℤ)
    (hZ : IsZero (Z.X (a - 1))) (hq : ∀ p q, q < 0 → IsZero ((Z.X p).X q)) (p q : ℤ)
    (hq0 : q < 0) : IsZero (((kernel (bottomProj Z a hZ)).X p).X q) :=
  isZero_kernel_bottomProj_X_X Z a hZ p q (hq p q hq0)

/-- The stupid truncation vanishes in first degrees `< a + 1`: below `a` because `Z` does, and in
the column `a` because that column is exactly what was deleted. -/
lemma isZero_bottomTrunc_X
    {Z : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)} (a : ℤ)
    (hZ : IsZero (Z.X (a - 1))) (hp : ∀ p, p < a → IsZero (Z.X p)) (p : ℤ) (hpa : p < a + 1) :
    IsZero ((kernel (bottomProj Z a hZ)).X p) := by
  by_cases h : p = a
  · rw [h]; exact isZero_kernel_bottomProj_X_self Z a hZ
  · exact isZero_kernel_bottomProj_X Z a hZ p (hp p (by lia))

variable {Z Z' : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)} (f : Z ⟶ Z')
  (a : ℤ) (hZ : IsZero (Z.X (a - 1))) (hZ' : IsZero (Z'.X (a - 1)))
  [Z.HasTotal (ComplexShape.up ℤ)] [Z'.HasTotal (ComplexShape.up ℤ)]
  [(kernel (bottomProj Z a hZ)).HasTotal (ComplexShape.up ℤ)]
  [(kernel (bottomProj Z' a hZ')).HasTotal (ComplexShape.up ℤ)]
  [(singleColumn (Z.X a) a).HasTotal (ComplexShape.up ℤ)]
  [(singleColumn (Z'.X a) a).HasTotal (ComplexShape.up ℤ)]

/-- **The morphism of short exact sequences of total complexes** induced by `f`: it is
`Tot` applied to the morphism of short exact sequences of double complexes whose middle
component is `f`, whose left component is `bottomTruncMap` and whose right component is `f.f a`
placed in the column `a`. -/
noncomputable def totalBottomSESMap :
    totalBottomSES Z a hZ ⟶ totalBottomSES Z' a hZ' where
  τ₁ := HomologicalComplex₂.total.map (bottomTruncMap f a hZ hZ') (ComplexShape.up ℤ)
  τ₂ := HomologicalComplex₂.total.map f (ComplexShape.up ℤ)
  τ₃ := HomologicalComplex₂.total.map
    ((HomologicalComplex.single (CochainComplex A ℤ) (ComplexShape.up ℤ) a).map (f.f a))
    (ComplexShape.up ℤ)
  comm₁₂ := by
    change HomologicalComplex₂.total.map (bottomTruncMap f a hZ hZ') (ComplexShape.up ℤ) ≫
        HomologicalComplex₂.total.map (kernel.ι (bottomProj Z' a hZ')) (ComplexShape.up ℤ) =
      HomologicalComplex₂.total.map (kernel.ι (bottomProj Z a hZ)) (ComplexShape.up ℤ) ≫
        HomologicalComplex₂.total.map f (ComplexShape.up ℤ)
    rw [← HomologicalComplex₂.total.map_comp, ← HomologicalComplex₂.total.map_comp,
      bottomTruncMap_ι]
  comm₂₃ := by
    change HomologicalComplex₂.total.map f (ComplexShape.up ℤ) ≫
        HomologicalComplex₂.total.map (bottomProj Z' a hZ') (ComplexShape.up ℤ) =
      HomologicalComplex₂.total.map (bottomProj Z a hZ) (ComplexShape.up ℤ) ≫
        HomologicalComplex₂.total.map ((HomologicalComplex.single (CochainComplex A ℤ)
          (ComplexShape.up ℤ) a).map (f.f a)) (ComplexShape.up ℤ)
    rw [← HomologicalComplex₂.total.map_comp, ← HomologicalComplex₂.total.map_comp,
      bottomProj_naturality]

/-- The left component of `totalBottomSESMap` is `Tot` of `bottomTruncMap`. -/
lemma totalBottomSESMap_τ₁ : (totalBottomSESMap f a hZ hZ').τ₁ =
    HomologicalComplex₂.total.map (bottomTruncMap f a hZ hZ') (ComplexShape.up ℤ) := rfl

/-- The middle component of `totalBottomSESMap` is `Tot` of `f`. -/
lemma totalBottomSESMap_τ₂ : (totalBottomSESMap f a hZ hZ').τ₂ =
    HomologicalComplex₂.total.map f (ComplexShape.up ℤ) := rfl

/-- The right component of `totalBottomSESMap` is `Tot` of `f.f a` placed in the column `a`. -/
lemma totalBottomSESMap_τ₃ : (totalBottomSESMap f a hZ hZ').τ₃ =
    HomologicalComplex₂.total.map ((HomologicalComplex.single (CochainComplex A ℤ)
      (ComplexShape.up ℤ) a).map (f.f a)) (ComplexShape.up ℤ) := rfl

end BottomMap

section BottomInduction

/-- **Below the bound the total complexes vanish**, so there the map induced on homology is an
isomorphism: this is the base of both inductions. -/
lemma isIso_homologyMap_total_map_of_lt
    {Z Z' : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)} (f : Z ⟶ Z')
    (a n : ℤ) (hq : ∀ p q, q < 0 → IsZero ((Z.X p).X q)) (hp : ∀ p, p < a → IsZero (Z.X p))
    (hq' : ∀ p q, q < 0 → IsZero ((Z'.X p).X q)) (hp' : ∀ p, p < a → IsZero (Z'.X p))
    [Z.HasTotal (ComplexShape.up ℤ)] [Z'.HasTotal (ComplexShape.up ℤ)] (hn : n < a) :
    IsIso (HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map f (ComplexShape.up ℤ)) n) :=
  isIso_of_isZero _ (isZero_homology_of_isZero_X n (isZero_total_X Z a hq hp n hn))
    (isZero_homology_of_isZero_X n (isZero_total_X Z' a hq' hp' n hn))

/-- **Pass 1 of the induction**: `Tot(f)` induces a monomorphism on `H^n`, by induction on
`n - a`. Deleting the bottom column presents `Tot(f)` as the middle term of a morphism of short
exact sequences whose right-hand term is a quasi-isomorphism and whose left-hand term is the
same problem for the truncation `Z^{≥ a + 1}`, one step further along the induction. The four
lemma bounds monomorphy in degree `n` of the middle term by epimorphy in degree `n - 1` and
monomorphy in degree `n` of the outer terms, so nothing about the degrees above `n` is needed and
this pass closes on its own. -/
lemma mono_homologyMap_total_map_aux (k : ℕ) :
    ∀ {Z Z' : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)} (f : Z ⟶ Z')
      (a n : ℤ), (∀ p q, q < 0 → IsZero ((Z.X p).X q)) → (∀ p, p < a → IsZero (Z.X p)) →
      (∀ p q, q < 0 → IsZero ((Z'.X p).X q)) → (∀ p, p < a → IsZero (Z'.X p)) →
      ∀ [Z.HasTotal (ComplexShape.up ℤ)] [Z'.HasTotal (ComplexShape.up ℤ)],
      (∀ p, QuasiIso (f.f p)) → (n - a + 1).toNat ≤ k →
        Mono (HomologicalComplex.homologyMap
          (HomologicalComplex₂.total.map f (ComplexShape.up ℤ)) n) := by
  induction k with
  | zero =>
    intro Z Z' f a n hq hp hq' hp' _ _ _ hk
    have := isIso_homologyMap_total_map_of_lt f a n hq hp hq' hp' (by omega)
    infer_instance
  | succ k ih =>
    intro Z Z' f a n hq hp hq' hp' _ _ hf hk
    by_cases hn : n < a
    · have := isIso_homologyMap_total_map_of_lt f a n hq hp hq' hp' hn
      infer_instance
    have hZ : IsZero (Z.X (a - 1)) := hp _ (by lia)
    have hZ' : IsZero (Z'.X (a - 1)) := hp' _ (by lia)
    have := hasTotal_kernel_bottomProj Z a hZ hq hp
    have := hasTotal_kernel_bottomProj Z' a hZ' hq' hp'
    have := hasTotal_singleColumn (Z.X a) a
    have := hasTotal_singleColumn (Z'.X a) a
    have hSE₁ := totalBottomSES_shortExact Z a hZ
    have hSE₂ := totalBottomSES_shortExact Z' a hZ'
    have := hf a
    have : QuasiIso (totalBottomSESMap f a hZ hZ').τ₃ := by
      rw [totalBottomSESMap_τ₃]
      exact quasiIso_total_map_singleColumn (f.f a) a
    have hτ₁ : Mono (HomologicalComplex.homologyMap (totalBottomSESMap f a hZ hZ').τ₁ n) := by
      rw [totalBottomSESMap_τ₁]
      exact ih (bottomTruncMap f a hZ hZ') (a + 1) n (isZero_bottomTrunc_X_X a hZ hq)
        (isZero_bottomTrunc_X a hZ hp) (isZero_bottomTrunc_X_X a hZ' hq')
        (isZero_bottomTrunc_X a hZ' hp') (quasiIso_bottomTruncMap_f f a hZ hZ' hf) (by omega)
    have hrel : (ComplexShape.up ℤ).Rel (n - 1) n := by simp
    rw [← totalBottomSESMap_τ₂ f a hZ hZ']
    refine Abelian.mono_of_epi_of_mono_of_mono
      ((ComposableArrows.δ₀Functor ⋙ ComposableArrows.δ₀Functor).map
        (HomologySequence.mapComposableArrows₅ (totalBottomSESMap f a hZ hZ') hSE₁ hSE₂
          (n - 1) n hrel))
      ((HomologySequence.composableArrows₅_exact hSE₁ (n - 1) n hrel).δ₀.δ₀)
      ((HomologySequence.composableArrows₅_exact hSE₂ (n - 1) n hrel).δ₀.δ₀) ?_ hτ₁ ?_
    · exact (inferInstance :
        Epi (HomologicalComplex.homologyMap (totalBottomSESMap f a hZ hZ').τ₃ (n - 1)))
    · exact (inferInstance :
        Mono (HomologicalComplex.homologyMap (totalBottomSESMap f a hZ hZ').τ₃ n))

/-- Pass 1 of the induction, with the bound discharged. -/
lemma mono_homologyMap_total_map
    {Z Z' : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)} (f : Z ⟶ Z')
    (a n : ℤ) (hq : ∀ p q, q < 0 → IsZero ((Z.X p).X q)) (hp : ∀ p, p < a → IsZero (Z.X p))
    (hq' : ∀ p q, q < 0 → IsZero ((Z'.X p).X q)) (hp' : ∀ p, p < a → IsZero (Z'.X p))
    [Z.HasTotal (ComplexShape.up ℤ)] [Z'.HasTotal (ComplexShape.up ℤ)]
    (hf : ∀ p, QuasiIso (f.f p)) :
    Mono (HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map f (ComplexShape.up ℤ)) n) :=
  mono_homologyMap_total_map_aux (n - a + 1).toNat f a n hq hp hq' hp' hf le_rfl

/-- **Pass 2 of the induction**: `Tot(f)` induces an epimorphism on `H^n`. The second four lemma
bounds epimorphy in degree `n` of the middle term by epimorphy in degree `n` of the outer terms
and monomorphy in degree `n + 1` of the left-hand one, which is why the induction has to be run
twice: the monomorphy one degree up is supplied by pass 1, which is already available in every
degree. -/
lemma epi_homologyMap_total_map_aux (k : ℕ) :
    ∀ {Z Z' : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)} (f : Z ⟶ Z')
      (a n : ℤ), (∀ p q, q < 0 → IsZero ((Z.X p).X q)) → (∀ p, p < a → IsZero (Z.X p)) →
      (∀ p q, q < 0 → IsZero ((Z'.X p).X q)) → (∀ p, p < a → IsZero (Z'.X p)) →
      ∀ [Z.HasTotal (ComplexShape.up ℤ)] [Z'.HasTotal (ComplexShape.up ℤ)],
      (∀ p, QuasiIso (f.f p)) → (n - a + 1).toNat ≤ k →
        Epi (HomologicalComplex.homologyMap
          (HomologicalComplex₂.total.map f (ComplexShape.up ℤ)) n) := by
  induction k with
  | zero =>
    intro Z Z' f a n hq hp hq' hp' _ _ _ hk
    have := isIso_homologyMap_total_map_of_lt f a n hq hp hq' hp' (by omega)
    infer_instance
  | succ k ih =>
    intro Z Z' f a n hq hp hq' hp' _ _ hf hk
    by_cases hn : n < a
    · have := isIso_homologyMap_total_map_of_lt f a n hq hp hq' hp' hn
      infer_instance
    have hZ : IsZero (Z.X (a - 1)) := hp _ (by lia)
    have hZ' : IsZero (Z'.X (a - 1)) := hp' _ (by lia)
    have := hasTotal_kernel_bottomProj Z a hZ hq hp
    have := hasTotal_kernel_bottomProj Z' a hZ' hq' hp'
    have := hasTotal_singleColumn (Z.X a) a
    have := hasTotal_singleColumn (Z'.X a) a
    have hSE₁ := totalBottomSES_shortExact Z a hZ
    have hSE₂ := totalBottomSES_shortExact Z' a hZ'
    have := hf a
    have : QuasiIso (totalBottomSESMap f a hZ hZ').τ₃ := by
      rw [totalBottomSESMap_τ₃]
      exact quasiIso_total_map_singleColumn (f.f a) a
    have hτ₁ : Epi (HomologicalComplex.homologyMap (totalBottomSESMap f a hZ hZ').τ₁ n) := by
      rw [totalBottomSESMap_τ₁]
      exact ih (bottomTruncMap f a hZ hZ') (a + 1) n (isZero_bottomTrunc_X_X a hZ hq)
        (isZero_bottomTrunc_X a hZ hp) (isZero_bottomTrunc_X_X a hZ' hq')
        (isZero_bottomTrunc_X a hZ' hp') (quasiIso_bottomTruncMap_f f a hZ hZ' hf) (by omega)
    have hτ₁' :
        Mono (HomologicalComplex.homologyMap (totalBottomSESMap f a hZ hZ').τ₁ (n + 1)) := by
      rw [totalBottomSESMap_τ₁]
      exact mono_homologyMap_total_map (bottomTruncMap f a hZ hZ') (a + 1) (n + 1)
        (isZero_bottomTrunc_X_X a hZ hq) (isZero_bottomTrunc_X a hZ hp)
        (isZero_bottomTrunc_X_X a hZ' hq') (isZero_bottomTrunc_X a hZ' hp')
        (quasiIso_bottomTruncMap_f f a hZ hZ' hf)
    have hrel : (ComplexShape.up ℤ).Rel n (n + 1) := by simp
    rw [← totalBottomSESMap_τ₂ f a hZ hZ']
    refine Abelian.epi_of_epi_of_epi_of_mono
      ((ComposableArrows.δlastFunctor ⋙ ComposableArrows.δlastFunctor).map
        (HomologySequence.mapComposableArrows₅ (totalBottomSESMap f a hZ hZ') hSE₁ hSE₂
          n (n + 1) hrel))
      ((HomologySequence.composableArrows₅_exact hSE₁ n (n + 1) hrel).δlast.δlast)
      ((HomologySequence.composableArrows₅_exact hSE₂ n (n + 1) hrel).δlast.δlast) hτ₁ ?_ hτ₁'
    · exact (inferInstance :
        Epi (HomologicalComplex.homologyMap (totalBottomSESMap f a hZ hZ').τ₃ n))

/-- Pass 2 of the induction, with the bound discharged. -/
lemma epi_homologyMap_total_map
    {Z Z' : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)} (f : Z ⟶ Z')
    (a n : ℤ) (hq : ∀ p q, q < 0 → IsZero ((Z.X p).X q)) (hp : ∀ p, p < a → IsZero (Z.X p))
    (hq' : ∀ p q, q < 0 → IsZero ((Z'.X p).X q)) (hp' : ∀ p, p < a → IsZero (Z'.X p))
    [Z.HasTotal (ComplexShape.up ℤ)] [Z'.HasTotal (ComplexShape.up ℤ)]
    (hf : ∀ p, QuasiIso (f.f p)) :
    Epi (HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map f (ComplexShape.up ℤ)) n) :=
  epi_homologyMap_total_map_aux (n - a + 1).toNat f a n hq hp hq' hp' hf le_rfl

end BottomInduction

/-- **[Stacks, Tag 0133]**, in the form of a statement about a morphism (Weibel's acyclic
assembly lemma): a morphism of double complexes which is a quasi-isomorphism on each column
induces a quasi-isomorphism on total complexes, provided both double complexes vanish in
negative second degrees and in first degrees `≪ 0`.

The source deduces the tag from the first spectral sequence of a double complex and its
convergence ([Stacks, Tag 0130], [Stacks, Tag 0132]), machinery which Mathlib does not have.
The route which does not need it is an induction on `n - a`, whose ingredients are the four
groups of lemmas above.

For `n < a` every summand of `Tot(Z)^n` vanishes (`isZero_total_X`), so the map is an
isomorphism on `H^n` there. For the step, delete the bottom column: `bottomSES` is the short
exact sequence of double complexes `0 → Z^{≥ a + 1} → Z → Z^{a, •} → 0`, with
`Z^{≥ a + 1} = Ker(bottomProj)` — so that the inclusion and the morphism induced by `f` are
`kernel.ι` and `kernel.map` — and it is short exact by `bottomSES_shortExact`. Its outer terms
are understood: `Z^{≥ a + 1}` satisfies the hypotheses with the bound `a + 1`
(`isZero_kernel_bottomProj_X`, `isZero_kernel_bottomProj_X_self`,
`hasTotal_kernel_bottomProj`), which is the induction hypothesis, and
`Tot(Z^{a, •}) = Z^{a, •}⟦-a⟧` (`totalSingleColumnUnit`, `isIso_totalSingleColumnUnit`), on
which `f` induces a quasi-isomorphism by hypothesis (`quasiIso_total_map_singleColumn`).
Two out of three for the middle term of a short exact sequence of complexes is `quasiIso_τ₂`.
Because the four lemma bounds mono in degree `n` by mono in degree `n` of the outer terms
alone, while iso in degree `n` needs mono in degree `n + 1`, the induction runs twice: first
for monomorphy in every degree, then for invertibility.

The passage from the short exact sequence of double complexes to the short exact sequence of
their total complexes is `totalBottomSES_shortExact`: in total degree `n` the sequence
`0 → Tot(Z^{≥ a + 1})^n → Tot(Z)^n → Tot(Z^{a, •})^n → 0` is the splitting off of the single
summand indexed by `(a, n - a)` from a coproduct with finitely many nonzero terms, hence split
(`totalBottomSplitting`), hence short exact
(`HomologicalComplex.shortExact_of_degreewise_shortExact` and
`CategoryTheory.ShortComplex.Splitting.shortExact`); its retraction is
`totalBottomRetraction`, the `HomologicalComplex₂.totalDesc` of the inverses of
`isIso_kernel_ι_bottomProj_f` off the column `a` and of zero on it, and its section is
`totalSingleColumnDesc` followed by `HomologicalComplex₂.ιTotal`.

The two passes are `mono_homologyMap_total_map` and `epi_homologyMap_total_map`; both consume
`totalBottomSES_shortExact`, the morphism `totalBottomSESMap` of short exact sequences induced by
`f`, and the four lemma of `CategoryTheory.Abelian` applied to the long exact homology sequences
`HomologicalComplex.HomologySequence.composableArrows₅`. Their induction is on
`(n - a + 1).toNat`, which drops by one when the bottom column is deleted because the truncation
satisfies the hypotheses with the bound `a + 1`. -/
lemma quasiIso_total_map
    {Z Z' : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)} (f : Z ⟶ Z')
    (a : ℤ) (hq : ∀ p q, q < 0 → IsZero ((Z.X p).X q)) (hp : ∀ p, p < a → IsZero (Z.X p))
    (hq' : ∀ p q, q < 0 → IsZero ((Z'.X p).X q)) (hp' : ∀ p, p < a → IsZero (Z'.X p))
    [Z.HasTotal (ComplexShape.up ℤ)] [Z'.HasTotal (ComplexShape.up ℤ)]
    (hf : ∀ p, QuasiIso (f.f p)) :
    QuasiIso (HomologicalComplex₂.total.map f (ComplexShape.up ℤ)) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have := mono_homologyMap_total_map f a n hq hp hq' hp' hf
  have := epi_homologyMap_total_map f a n hq hp hq' hp' hf
  exact isIso_of_mono_of_epi _

/-- A cochain complex placed in second degree `0`, as a double complex: the source of the
augmentation of a Cartan-Eilenberg resolution. -/
noncomputable abbrev singleRowZero (K : CochainComplex A ℤ) :
    HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K

variable (K : CochainComplex A ℤ)

/-- The double complex `singleRowZero K` vanishes in negative second degrees. -/
lemma isZero_singleRowZero_X_X (p q : ℤ) (hq : q < 0) :
    IsZero (((singleRowZero K).X p).X q) :=
  HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (K.X p) q (by lia)

/-- If `K` is strictly `≥ a`, then `singleRowZero K` vanishes in first degrees `< a`. -/
lemma isZero_singleRowZero_X (a p : ℤ) [K.IsStrictlyGE a] (hp : p < a) :
    IsZero ((singleRowZero K).X p) :=
  Functor.map_isZero (HomologicalComplex.single A (ComplexShape.up ℤ) 0)
    (CochainComplex.isZero_of_isStrictlyGE K a p hp)

variable [(singleRowZero K).HasTotal (ComplexShape.up ℤ)]

/-- The projection of `Tot(K[0])^n` onto its only possibly nonzero summand, the one indexed by
`(n, 0)`. -/
noncomputable def totalSingleRowZeroDesc (n : ℤ) :
    ((singleRowZero K).total (ComplexShape.up ℤ)).X n ⟶ K.X n :=
  (singleRowZero K).totalDesc (fun p q h =>
    if hq : q = 0 then
      eqToHom (by subst hq; have h' : p + 0 = n := h; rw [show p = n by lia]; rfl) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X n)).hom
    else (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (K.X p) q hq).to_ _)

/-- On the summand indexed by `(n, 0)`, `totalSingleRowZeroDesc` is the identification of that
summand with `K^n`. -/
lemma ι_totalSingleRowZeroDesc (n : ℤ) :
    (singleRowZero K).ιTotal (ComplexShape.up ℤ) n 0 n (by simp) ≫
        totalSingleRowZeroDesc K n =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X n)).hom := by
  rw [totalSingleRowZeroDesc, HomologicalComplex₂.ι_totalDesc]
  simp

/-- The canonical morphism `K ⟶ Tot(K[0])`, in degree `n` the inclusion of the summand
indexed by `(n, 0)`. It is an isomorphism. -/
noncomputable def totalSingleRowZeroUnit :
    K ⟶ (singleRowZero K).total (ComplexShape.up ℤ) where
  f n := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X n)).inv ≫
    (singleRowZero K).ιTotal (ComplexShape.up ℤ) n 0 n (by simp)
  comm' n n' h := by
    obtain rfl : n + 1 = n' := h
    have h2 : ((singleRowZero K).X n).d 0 (0 + 1) = 0 :=
      HomologicalComplex.single_obj_d _ _ _ _ _
    have h1 : ((singleRowZero K).d n (n + 1)).f 0 =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X n)).hom ≫
          K.d n (n + 1) ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X (n + 1))).inv :=
      HomologicalComplex.single_map_f_self _ _ _
    rw [Category.assoc, HomologicalComplex₂.ιTotal_d_up_ℤ _ n 0 n (add_zero n), h1, h2]
    simp

/-- Each component of `totalSingleRowZeroUnit K` is an isomorphism, with inverse
`totalSingleRowZeroDesc K n`. -/
lemma isIso_totalSingleRowZeroUnit_f (n : ℤ) :
    IsIso ((totalSingleRowZeroUnit K).f n) := by
  refine ⟨totalSingleRowZeroDesc K n, ?_, ?_⟩
  · dsimp [totalSingleRowZeroUnit]
    rw [Category.assoc, ι_totalSingleRowZeroDesc]
    simp
  · refine HomologicalComplex₂.total.hom_ext (ComplexShape.up ℤ) (fun p q h => ?_)
    have h' : p + q = n := h
    by_cases hq : q = 0
    · subst hq
      obtain rfl : p = n := by lia
      dsimp [totalSingleRowZeroUnit]
      rw [Category.comp_id, ← Category.assoc, ι_totalSingleRowZeroDesc]
      simp
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (K.X p) q
        hq).eq_of_src _ _

/-- The morphism `K ⟶ Tot(K[0])` is an isomorphism of cochain complexes. -/
lemma isIso_totalSingleRowZeroUnit : IsIso (totalSingleRowZeroUnit K) := by
  have := isIso_totalSingleRowZeroUnit_f K
  exact HomologicalComplex.Hom.isIso_of_components _

/-- `totalSingleRowZeroUnit` is natural in the complex: the isomorphism identifying a complex
with the total complex of that complex placed in second degree `0` is a natural one. -/
lemma totalSingleRowZeroUnit_naturality {K K' : CochainComplex A ℤ} (g : K ⟶ K')
    [(singleRowZero K).HasTotal (ComplexShape.up ℤ)]
    [(singleRowZero K').HasTotal (ComplexShape.up ℤ)] :
    totalSingleRowZeroUnit K ≫ HomologicalComplex₂.total.map
        (((HomologicalComplex.single A (ComplexShape.up ℤ) 0).mapHomologicalComplex
          (ComplexShape.up ℤ)).map g) (ComplexShape.up ℤ) =
      g ≫ totalSingleRowZeroUnit K' := by
  ext n
  dsimp [totalSingleRowZeroUnit]
  rw [Category.assoc, HomologicalComplex₂.ιTotal_map]
  dsimp
  rw [HomologicalComplex.single_map_f_self, ← Category.assoc, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp, Category.assoc]

end

end StacksDraft.TotalComplexQuasiIso

section

/-!
## Double complex gives a resolution

Given a complex `K^•` and a double complex `A^{•,•}` together with maps
`α^p : K^p → A^{p,0}` satisfying the standard hypotheses (finite diagonals,
vanishing for `q < 0`, column exactness, and isomorphism with the column
kernels), the induced map `K^• → Tot(A^{•,•})` is a quasi-isomorphism.
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The `0`-th row complex `A^{•,0}` of a double complex. -/
@[simps, implicit_reducible]
noncomputable def rowZero
    (DA : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)) :
    HomologicalComplex A (ComplexShape.up ℤ) where
  X p := (DA.X p).X 0
  d p p' := (DA.d p p').f 0
  shape p p' h := by rw [DA.shape p p' h, zero_f]
  d_comp_d' p p' p'' _ _ := by rw [← comp_f, DA.d_comp_d, zero_f]

/-- Diagonal finiteness: for every `n`, only finitely many `(p, q)` with
`p + q = n` have `A^{p,q}` nonzero. -/
@[ega "0 11.3.1"]
def DiagonalFinite
    (DA : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)) : Prop :=
  ∀ n : ℤ, { p : ℤ | ¬ IsZero ((DA.X p).X (n - p)) }.Finite

/-- The hypotheses for Stacks Tag 0133 (variant in the first variable `p`). -/
structure Hypotheses
    (K : HomologicalComplex A (ComplexShape.up ℤ))
    (DA : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (α : K ⟶ rowZero DA) : Prop where
  /-- Each antidiagonal of `DA` has only finitely many nonzero objects. -/
  diagonalFinite : DiagonalFinite DA
  /-- `DA` vanishes in negative second degrees. -/
  zero_of_neg : ∀ (p q : ℤ), q < 0 → IsZero ((DA.X p).X q)
  /-- Each column of `DA` is exact in every nonzero degree. -/
  exactAt_of_ne_zero : ∀ (p q : ℤ), q ≠ 0 → (DA.X p).ExactAt q
  /-- Each `α^p` identifies `K^p` with the kernel of `d : A^{p,0} → A^{p,1}`. -/
  inducesIsoKernel : ∀ (p : ℤ), ∃ hα : α.f p ≫ (DA.X p).d 0 1 = 0,
    IsIso (kernel.lift ((DA.X p).d 0 1) (α.f p) hα)

/-- A diagonally finite double complex has a total complex. -/
@[ega "0 11.3.1" "partial"]
lemma hasTotal_of_diagonalFinite
    (DA : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (h : DiagonalFinite DA) :
    DA.HasTotal (ComplexShape.up ℤ) := by
  apply HomologicalComplex₂.hasTotal_of_finite
  intro n
  refine ((h n).image (fun p => (p, n - p))).subset ?_
  rintro ⟨p, q⟩ ⟨hpq, hz⟩
  have heq : n - p = q := by simp at hpq; omega
  exact ⟨p, by simpa [heq] using hz, by simp [heq]⟩

/-- A double complex whose flip is diagonally finite has a total complex. -/
@[ega "0 11.3.1" "partial"]
lemma hasTotal_of_diagonalFinite_flip
    (DA : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (h : DiagonalFinite DA.flip) :
    DA.HasTotal (ComplexShape.up ℤ) :=
  (DA.flip_hasTotal_iff (ComplexShape.up ℤ)).mp (hasTotal_of_diagonalFinite DA.flip h)

open StacksDraft.TotalComplexQuasiIso

private lemma trunc_zero_neg
    (Z : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (a : ℤ)
    (hz : ∀ p q, q < 0 → IsZero ((Z.X p).X q)) :
    ∀ p q, q < 0 → IsZero (((Z.stupidTrunc (ComplexShape.embeddingUpIntGE a)).X p).X q) := by
  intro p q hq
  by_cases hp : ∃ i, (ComplexShape.embeddingUpIntGE a).f i = p
  · obtain ⟨i, hi⟩ := hp
    exact (hz p q hq).of_iso
      ((HomologicalComplex.eval A _ q).mapIso (Z.stupidTruncXIso _ hi))
  · exact (HomologicalComplex.eval A _ q).map_isZero
      (Z.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE a) p (by simpa using hp))

private lemma trunc_zero_lt
    (Z : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (a : ℤ) :
    ∀ p, p < a → IsZero ((Z.stupidTrunc (ComplexShape.embeddingUpIntGE a)).X p) :=
  fun p hp => Z.isZero_stupidTrunc_X _ p (by
    simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using hp)

private lemma trunc_map_quasiIso
    {Z Z' : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    (f : Z ⟶ Z') (a : ℤ) (hf : ∀ p, QuasiIso (f.f p)) :
    ∀ p, QuasiIso ((stupidTruncMap f (ComplexShape.embeddingUpIntGE a)).f p) := by
  intro p
  by_cases hp : ∃ i, (ComplexShape.embeddingUpIntGE a).f i = p
  · obtain ⟨i, hi⟩ := hp
    have := hf p
    have heq := stupidTruncMap_stupidTruncXIso_hom f (ComplexShape.embeddingUpIntGE a) hi
    have : QuasiIso ((stupidTruncMap f (ComplexShape.embeddingUpIntGE a)).f p ≫
        (Z'.stupidTruncXIso _ hi).hom) := by rw [heq]; infer_instance
    exact quasiIso_of_comp_right _ (Z'.stupidTruncXIso _ hi).hom
  · have := isIso_of_isZero ((stupidTruncMap f (ComplexShape.embeddingUpIntGE a)).f p)
      (Z.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE a) p (by simpa using hp))
      (Z'.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE a) p (by simpa using hp))
    infer_instance

private lemma isIso_total_map_f
    {Z Z' : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    (f : Z ⟶ Z') [Z.HasTotal (ComplexShape.up ℤ)] [Z'.HasTotal (ComplexShape.up ℤ)]
    (n : ℤ) (hf : ∀ p q, p + q = n → IsIso ((f.f p).f q)) :
    IsIso ((HomologicalComplex₂.total.map f (ComplexShape.up ℤ)).f n) := by
  let g := Z'.totalDesc (fun p q hpq =>
    have := hf p q hpq
    inv ((f.f p).f q) ≫ Z.ιTotal (ComplexShape.up ℤ) p q n hpq)
  refine ⟨g, ?_, ?_⟩
  · apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    have := hf p q hpq
    simp [g, HomologicalComplex₂.ιTotal_map_assoc]
  · apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    have := hf p q hpq
    simp [g, HomologicalComplex₂.ιTotal_map]

private lemma isIso_total_trunc_f
    (Z : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (a n : ℤ)
    [Z.HasTotal (ComplexShape.up ℤ)]
    [HomologicalComplex₂.HasTotal (Z.stupidTrunc (ComplexShape.embeddingUpIntGE a))
      (ComplexShape.up ℤ)]
    (hz : ∀ p, p < a → IsZero ((Z.X p).X (n - p))) :
    IsIso ((HomologicalComplex₂.total.map
      (ιStupidTrunc Z (ComplexShape.embeddingUpIntGE a)) (ComplexShape.up ℤ)).f n) := by
  apply isIso_total_map_f
  intro p q hpq
  by_cases hp : a ≤ p
  · have := isIso_ιStupidTrunc_f Z (ComplexShape.embeddingUpIntGE a)
      (i := (p - a).toNat) (i' := p) (by rw [ComplexShape.embeddingUpIntGE_f]; omega)
    infer_instance
  · have hlt : p < a := by omega
    have hq : q = n - p := by omega
    exact isIso_of_isZero _
      ((HomologicalComplex.eval A _ q).map_isZero (trunc_zero_lt Z a p hlt))
      (by rw [hq]; exact hz p hlt)

private lemma quasiIsoAt_of_three_isIso {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℤ)
    [IsIso (f.f (n - 1))] [IsIso (f.f n)] [IsIso (f.f (n + 1))] : QuasiIsoAt f n := by
  rw [quasiIsoAt_iff' f (n - 1) n (n + 1) (by simp) (by simp)]
  have : IsIso ((shortComplexFunctor' A (ComplexShape.up ℤ) (n - 1) n (n + 1)).map f) :=
    @ShortComplex.isIso_of_isIso _ _ _ _ _ _
      (inferInstanceAs (IsIso (f.f (n - 1))))
      (inferInstanceAs (IsIso (f.f n))) (inferInstanceAs (IsIso (f.f (n + 1))))
  infer_instance

/-- In a fixed degree, truncate below the supports of the three adjacent diagonals.
The resulting total complexes agree in those degrees, and the bounded comparison
theorem applies to the truncations. -/
private lemma quasiIso_total_map_diagonalFinite
    {Z Z' : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    (f : Z ⟶ Z') (hZ : DiagonalFinite Z) (hZ' : DiagonalFinite Z')
    (hq : ∀ p q, q < 0 → IsZero ((Z.X p).X q))
    (hq' : ∀ p q, q < 0 → IsZero ((Z'.X p).X q))
    [Z.HasTotal (ComplexShape.up ℤ)] [Z'.HasTotal (ComplexShape.up ℤ)]
    (hf : ∀ p, QuasiIso (f.f p)) :
    QuasiIso (HomologicalComplex₂.total.map f (ComplexShape.up ℤ)) := by
  refine ⟨fun n => ?_⟩
  let S := {p : ℤ | ¬ IsZero ((Z.X p).X (n - 1 - p))} ∪
    {p : ℤ | ¬ IsZero ((Z.X p).X (n - p))} ∪
    {p : ℤ | ¬ IsZero ((Z.X p).X (n + 1 - p))} ∪
    {p : ℤ | ¬ IsZero ((Z'.X p).X (n - 1 - p))} ∪
    {p : ℤ | ¬ IsZero ((Z'.X p).X (n - p))} ∪
    {p : ℤ | ¬ IsZero ((Z'.X p).X (n + 1 - p))}
  have hS : S.Finite :=
    (((((hZ (n - 1)).union (hZ n)).union (hZ (n + 1))).union (hZ' (n - 1))).union
      (hZ' n)).union (hZ' (n + 1))
  obtain ⟨a, ha⟩ := hS.bddBelow
  have hz : ∀ m ∈ [n - 1, n, n + 1], ∀ p, p < a →
      IsZero ((Z.X p).X (m - p)) ∧ IsZero ((Z'.X p).X (m - p)) := by
    intro m hm p hp
    have hpS : p ∉ S := fun h => not_le_of_gt hp (ha h)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> constructor <;> by_contra hh <;> exact hpS (by simp [S, hh])
  let e := ComplexShape.embeddingUpIntGE a
  have := hasTotal_of_bounded (Z.stupidTrunc e) a (trunc_zero_neg Z a hq) (trunc_zero_lt Z a)
  have := hasTotal_of_bounded (Z'.stupidTrunc e) a (trunc_zero_neg Z' a hq') (trunc_zero_lt Z' a)
  have := quasiIso_total_map (stupidTruncMap f e) a
    (trunc_zero_neg Z a hq) (trunc_zero_lt Z a)
    (trunc_zero_neg Z' a hq') (trunc_zero_lt Z' a) (trunc_map_quasiIso f a hf)
  have hQ : ∀ (Y : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ))
      [Y.HasTotal (ComplexShape.up ℤ)]
      [HomologicalComplex₂.HasTotal (Y.stupidTrunc e) (ComplexShape.up ℤ)],
      (∀ m ∈ [n - 1, n, n + 1], ∀ p, p < a → IsZero ((Y.X p).X (m - p))) →
      QuasiIsoAt (HomologicalComplex₂.total.map (ιStupidTrunc Y e) (ComplexShape.up ℤ)) n := by
    intro Y _ _ hY
    have := isIso_total_trunc_f Y a (n - 1) (hY _ (by simp))
    have := isIso_total_trunc_f Y a n (hY _ (by simp))
    have := isIso_total_trunc_f Y a (n + 1) (hY _ (by simp))
    exact quasiIsoAt_of_three_isIso _ n
  have := hQ Z fun m hm p hp => (hz m hm p hp).1
  have := hQ Z' fun m hm p hp => (hz m hm p hp).2
  have heq := congrArg (fun g => HomologicalComplex₂.total.map g (ComplexShape.up ℤ))
    (stupidTruncMap_ιStupidTrunc (ComplexShape.embeddingUpIntGE a) f)
  simp only [HomologicalComplex₂.total.map_comp] at heq
  have : QuasiIsoAt
      (HomologicalComplex₂.total.map (ιStupidTrunc Z e) (ComplexShape.up ℤ) ≫
        HomologicalComplex₂.total.map f (ComplexShape.up ℤ)) n := by
    rw [← heq]
    infer_instance
  exact quasiIsoAt_of_comp_left
    (HomologicalComplex₂.total.map (ιStupidTrunc Z e) (ComplexShape.up ℤ))
    (HomologicalComplex₂.total.map f (ComplexShape.up ℤ)) n

private noncomputable def columnAugmentation
    (K : CochainComplex A ℤ)
    (DA : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (α : K ⟶ rowZero DA) (h : Hypotheses K DA α) (p : ℤ) :
    (singleRowZero K).X p ⟶ DA.X p :=
  mkHomFromSingle (α.f p) (fun q hq => by
    obtain rfl : q = 1 := by
      simp at hq
      omega
    exact (h.inducesIsoKernel p).choose)

private lemma columnAugmentation_f_zero
    (K : CochainComplex A ℤ)
    (DA : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (α : K ⟶ rowZero DA) (h : Hypotheses K DA α) (p : ℤ) :
    (columnAugmentation K DA α h p).f 0 =
      (singleObjXSelf (ComplexShape.up ℤ) 0 (K.X p)).hom ≫ α.f p := by
  apply mkHomFromSingle_f

@[simps]
private noncomputable def bicomplexAugmentation
    (K : CochainComplex A ℤ)
    (DA : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (α : K ⟶ rowZero DA) (h : Hypotheses K DA α) : singleRowZero K ⟶ DA where
  f := columnAugmentation K DA α h
  comm' p p' hp := by
    ext q
    by_cases hq : q = 0
    · subst hq
      simp only [comp_f, columnAugmentation_f_zero]
      rw [Functor.mapHomologicalComplex_obj_d, single_map_f_self]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      exact congrArg ((singleObjXSelf (ComplexShape.up ℤ) 0 (K.X p)).hom ≫ ·)
        (α.comm p p')
    · exact (isZero_single_obj_X (ComplexShape.up ℤ) 0 (K.X p) q hq).eq_of_src _ _

private lemma columnAugmentation_quasiIso
    (K : CochainComplex A ℤ)
    (DA : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (α : K ⟶ rowZero DA) (h : Hypotheses K DA α) (p : ℤ) :
    QuasiIso (columnAugmentation K DA α h p) := by
  refine ⟨fun q => ?_⟩
  by_cases hq : q = 0
  · subst hq
    let S := (singleRowZero K).X p
    let g := columnAugmentation K DA α h p
    obtain ⟨hw, hι⟩ := h.inducesIsoKernel p
    have : IsIso (kernel.lift ((DA.X p).d 0 1) (α.f p) hw) := hι
    have := S.isIso_iCycles 0 1 (by simp) (single_obj_d _ _ _ _ _)
    have := S.isIso_homologyπ (-1) 0 (by simp) (single_obj_d _ _ _ _ _)
    have := (DA.X p).isIso_homologyπ (-1) 0 (by simp)
      ((h.zero_of_neg p (-1) (by omega)).eq_of_src _ _)
    let hK := (DA.X p).cyclesIsKernel 0 1 (by simp)
    let e : (DA.X p).cycles 0 ≅ kernel ((DA.X p).d 0 1) :=
      IsLimit.conePointUniqueUpToIso hK (limit.isLimit _)
    have heq : cyclesMap g 0 ≫ e.hom =
        S.iCycles 0 ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 (K.X p)).hom ≫
          kernel.lift ((DA.X p).d 0 1) (α.f p) hw := by
      apply (cancel_mono (kernel.ι ((DA.X p).d 0 1))).mp
      have he : e.hom ≫ kernel.ι ((DA.X p).d 0 1) = (DA.X p).iCycles 0 :=
        IsLimit.conePointUniqueUpToIso_hom_comp hK (limit.isLimit _) WalkingParallelPair.zero
      simp only [Category.assoc, he, kernel.lift_ι, cyclesMap_i]
      rw [columnAugmentation_f_zero]
    have : IsIso (cyclesMap g 0 ≫ e.hom) := by
      rw [heq]
      infer_instance
    have : IsIso (cyclesMap g 0) := IsIso.of_isIso_comp_right _ e.hom
    have : IsIso (S.homologyπ 0 ≫ homologyMap g 0) := by
      rw [homologyπ_naturality]
      infer_instance
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact IsIso.of_isIso_comp_left (S.homologyπ 0) _
  · exact (quasiIsoAt_iff_exactAt _ q (HomologicalComplex.ExactAt.of_isZero
      (isZero_single_obj_X (ComplexShape.up ℤ) 0 (K.X p) q hq))).mpr
      (h.exactAt_of_ne_zero p q hq)

private lemma singleRowZero_diagonalFinite (K : CochainComplex A ℤ) :
    DiagonalFinite (singleRowZero K) := by
  intro n
  refine (Set.finite_singleton n).subset ?_
  intro p hp
  by_contra hn
  have hnp : n - p ≠ 0 := by rw [Set.mem_singleton_iff] at hn; omega
  exact hp (isZero_single_obj_X (ComplexShape.up ℤ) 0 (K.X p) (n - p) hnp)

/-- Under `Hypotheses K DA α`, given a total complex of `DA`, there is a quasi-isomorphism
`K^• ⟶ Tot(DA)` whose component in degree `n` is `α^n` followed by the inclusion of the
summand `(n, 0)`. -/
lemma exists_comparisonMap_p
    (K : HomologicalComplex A (ComplexShape.up ℤ))
    (DA : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (α : K ⟶ rowZero DA)
    (h : Hypotheses K DA α)
    (htot : DA.HasTotal (ComplexShape.up ℤ)) :
    ∃ (f : K ⟶
        (haveI : DA.HasTotal (ComplexShape.up ℤ) := htot;
         DA.total (ComplexShape.up ℤ))),
      (∀ n : ℤ, f.f n = α.f n ≫
          (haveI : DA.HasTotal (ComplexShape.up ℤ) := htot;
           DA.ιTotal (ComplexShape.up ℤ) n 0 n (by simp))) ∧
      QuasiIso f := by
  have := htot
  have := hasTotal_of_diagonalFinite (singleRowZero K) (singleRowZero_diagonalFinite K)
  have := quasiIso_total_map_diagonalFinite (bicomplexAugmentation K DA α h)
    (singleRowZero_diagonalFinite K) h.diagonalFinite
    (isZero_singleRowZero_X_X K) h.zero_of_neg (columnAugmentation_quasiIso K DA α h)
  have := isIso_totalSingleRowZeroUnit K
  refine ⟨totalSingleRowZeroUnit K ≫
    HomologicalComplex₂.total.map (bicomplexAugmentation K DA α h) (ComplexShape.up ℤ), ?_,
    inferInstance⟩
  intro n
  dsimp [totalSingleRowZeroUnit]
  rw [Category.assoc, HomologicalComplex₂.ιTotal_map, bicomplexAugmentation_f,
    columnAugmentation_f_zero]
  simp

/-- Under `Hypotheses K DA.flip α`, given a total complex of `DA`, there is a
quasi-isomorphism `K^• ⟶ Tot(DA)` whose component in degree `n` is `α^n` followed by the
inclusion of the summand `(0, n)`. -/
lemma exists_comparisonMap_q
    (K : HomologicalComplex A (ComplexShape.up ℤ))
    (DA : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (α : K ⟶ rowZero DA.flip)
    (h : Hypotheses K DA.flip α)
    (htot : DA.HasTotal (ComplexShape.up ℤ)) :
    ∃ (f : K ⟶
        (haveI : DA.HasTotal (ComplexShape.up ℤ) := htot;
         DA.total (ComplexShape.up ℤ))),
      (∀ n : ℤ, f.f n = α.f n ≫
          (haveI : DA.HasTotal (ComplexShape.up ℤ) := htot;
           DA.ιTotal (ComplexShape.up ℤ) 0 n n (by simp))) ∧
      QuasiIso f := by
  have := htot
  obtain ⟨f, hf, hq⟩ := exists_comparisonMap_p K DA.flip α h inferInstance
  have : QuasiIso f := hq
  refine ⟨f ≫ (DA.totalFlipIso (ComplexShape.up ℤ)).hom, ?_, inferInstance⟩
  intro n
  simp only [comp_f, hf, Category.assoc, HomologicalComplex₂.ιTotal_totalFlipIso_f_hom]
  simp

/-- Under the hypotheses, the total complex of `DA` exists and the induced
map `K^• → Tot(A^{•,•})` is a quasi-isomorphism (variant in the first
variable `p`). -/
@[stacks 0133 "p"]
theorem quasiIso_total_of_resolution
    (K : HomologicalComplex A (ComplexShape.up ℤ))
    (DA : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (α : K ⟶ rowZero DA)
    (h : Hypotheses K DA α) :
    ∃ _ : DA.HasTotal (ComplexShape.up ℤ),
      ∃ (f : K ⟶ DA.total (ComplexShape.up ℤ)),
        (∀ n : ℤ, f.f n =
          α.f n ≫ DA.ιTotal (ComplexShape.up ℤ) n 0 n (by simp)) ∧
          QuasiIso f :=
  ⟨hasTotal_of_diagonalFinite DA h.diagonalFinite, exists_comparisonMap_p K DA α h _⟩

/-- Under the hypotheses for `DA.flip`, the total complex of `DA` exists and the induced
map `K^• → Tot(A^{•,•})` is a quasi-isomorphism (variant in the second variable `q`). -/
@[stacks 0133 "q"]
theorem quasiIso_total_of_resolution_flip
    (K : HomologicalComplex A (ComplexShape.up ℤ))
    (DA : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (α : K ⟶ rowZero DA.flip)
    (h : Hypotheses K DA.flip α) :
    ∃ _ : DA.HasTotal (ComplexShape.up ℤ),
      ∃ (f : K ⟶ DA.total (ComplexShape.up ℤ)),
        (∀ n : ℤ, f.f n =
          α.f n ≫ DA.ιTotal (ComplexShape.up ℤ) 0 n n (by simp)) ∧
          QuasiIso f :=
  ⟨hasTotal_of_diagonalFinite_flip DA h.diagonalFinite, exists_comparisonMap_q K DA α h _⟩

variable (K : HomologicalComplex A (ComplexShape.up ℤ))
  (DA : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  (α : K ⟶ rowZero DA) (h : Hypotheses K DA α)
  [DA.HasTotal (ComplexShape.up ℤ)]

/-! ### The comparison map of [Stacks, Tag 0133] as data

`quasiIso_total_of_resolution` delivers the comparison `K^• ⟶ Tot(A^{•,•})` as an *existential*
with a chosen witness, and a chosen witness cannot be made natural in anything after the fact.
What makes it unnecessary is that the existential of `exists_comparisonMap_p` pins *every*
component of the witness: it says `f.f n = α.f n ≫ ιTotal n 0 n`.  So the comparison can be
**defined** by those components -- its `comm'` is the witness's, read off -- and then the witness
*equals* the definition, by `HomologicalComplex.hom_ext`, which transfers `QuasiIso` to it.

Being defined by the augmentation, the comparison is natural wherever the augmentation is:
`comparisonMapP_naturality` reduces the square for a morphism of the data to the square for the
augmentation, through `HomologicalComplex₂.ιTotal_map`. -/

/-- **A morphism of double complexes acts on the row `j = 0`.**  Its components are those of the
morphism in inner degree `0`, and its commutation is the morphism's in that degree. -/
noncomputable def rowZeroMap
    {DA DB : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    (ψ : DA ⟶ DB) : rowZero DA ⟶ rowZero DB where
  f p := (ψ.f p).f 0
  comm' p p' _ := congrArg (fun u => HomologicalComplex.Hom.f u 0) (ψ.comm p p')

/-- **`rowZero` is a functor**, namely `mapHomologicalComplex` of evaluation in inner degree
`0`; its action on morphisms is `rowZeroMap`. -/
noncomputable def rowZeroFunctor (A : Type u) [Category.{v} A] [Abelian A] :
    HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⥤
      HomologicalComplex A (ComplexShape.up ℤ) :=
  (HomologicalComplex.eval A (ComplexShape.up ℤ) (0 : ℤ)).mapHomologicalComplex
    (ComplexShape.up ℤ)

/-- `rowZeroFunctor` sends a double complex to its row `0`. -/
lemma rowZeroFunctor_obj {A : Type u} [Category.{v} A] [Abelian A]
    (DA : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)) :
    (rowZeroFunctor A).obj DA = rowZero DA := rfl

/-- `rowZeroFunctor` acts on morphisms as `rowZeroMap`, i.e. by `(ψ.f p).f 0`. -/
lemma rowZeroFunctor_map {A : Type u} [Category.{v} A] [Abelian A]
    {DA DB : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)} (ψ : DA ⟶ DB) :
    (rowZeroFunctor A).map ψ = rowZeroMap ψ := rfl

/-- **The comparison map of [Stacks, Tag 0133], as data.**  Its component in degree `n` is the
augmentation followed by the inclusion of the summand `A^{n,0}` of `Tot^n`, which is what
`exists_comparisonMap_p` says of its chosen witness; the commutation with the differentials is
that witness's. -/
noncomputable def comparisonMapP : K ⟶ DA.total (ComplexShape.up ℤ) where
  f n := α.f n ≫ DA.ιTotal (ComplexShape.up ℤ) n 0 n (by simp)
  comm' i j hij := by
    have hf := (exists_comparisonMap_p K DA α h inferInstance).choose_spec
    have hc := (exists_comparisonMap_p K DA α h inferInstance).choose.comm' i j hij
    rwa [hf.1 i, hf.1 j] at hc

/-- The components of `comparisonMapP` are the augmentation into the row `j = 0`. -/
@[simp]
lemma comparisonMapP_f (n : ℤ) :
    (comparisonMapP K DA α h).f n =
      α.f n ≫ DA.ιTotal (ComplexShape.up ℤ) n 0 n (by simp) :=
  rfl

/-- **The chosen witness of `exists_comparisonMap_p` is `comparisonMapP`.**  The existential pins
every component of the witness, and a morphism of complexes is determined by its components. -/
lemma choose_exists_comparisonMap_p_eq :
    (exists_comparisonMap_p K DA α h inferInstance).choose = comparisonMapP K DA α h :=
  HomologicalComplex.hom_ext _ _
    fun n => (exists_comparisonMap_p K DA α h inferInstance).choose_spec.1 n

/-- **[Stacks, Tag 0133], as data**: the comparison map `comparisonMapP` -- not merely some
morphism with its components -- is a quasi-isomorphism. -/
instance quasiIso_comparisonMapP : QuasiIso (comparisonMapP K DA α h) := by
  rw [← choose_exists_comparisonMap_p_eq K DA α h]
  exact (exists_comparisonMap_p K DA α h inferInstance).choose_spec.2

/-- **`H^n(K^•) ≅ H^n(Tot(A^{•,•}))`**, the isomorphism `comparisonMapP` induces on
cohomology. -/
noncomputable def comparisonHomologyIso (n : ℤ) :
    K.homology n ≅ (DA.total (ComplexShape.up ℤ)).homology n :=
  haveI : IsIso (HomologicalComplex.homologyMap (comparisonMapP K DA α h) n) :=
    (quasiIsoAt_iff_isIso_homologyMap (comparisonMapP K DA α h) n).1 inferInstance
  asIso (HomologicalComplex.homologyMap (comparisonMapP K DA α h) n)

/-- **The comparison map of [Stacks, Tag 0133] is natural.**  Given a morphism `φ : K^• ⟶ L^•` of
complexes and `ψ : A^{•,•} ⟶ B^{•,•}` of double complexes compatible with the two augmentations,
the square relating the two comparison maps commutes.

`comparisonMapP` is defined by the augmentation, so composing with `Tot(ψ)` only moves `ψ` past
the inclusion of a summand -- `HomologicalComplex₂.ιTotal_map` -- after which the square is the
hypothesis `hcomm` read in degree `n`.  This is what the existential form of
`quasiIso_total_of_resolution` cannot give. -/
theorem comparisonMapP_naturality
    {L : HomologicalComplex A (ComplexShape.up ℤ)}
    {DB : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    [DB.HasTotal (ComplexShape.up ℤ)]
    {β : L ⟶ rowZero DB} (hL : Hypotheses L DB β) (φ : K ⟶ L) (ψ : DA ⟶ DB)
    (hcomm : α ≫ rowZeroMap ψ = φ ≫ β) :
    comparisonMapP K DA α h ≫ HomologicalComplex₂.total.map ψ (ComplexShape.up ℤ) =
      φ ≫ comparisonMapP L DB β hL := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  have hn : α.f n ≫ (ψ.f n).f 0 = φ.f n ≫ β.f n :=
    congrArg (fun u => HomologicalComplex.Hom.f u n) hcomm
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, comparisonMapP_f, comparisonMapP_f,
    Category.assoc, HomologicalComplex₂.ιTotal_map, ← Category.assoc, hn, Category.assoc]

end

section

/-!
## Stacks tag 0FKH

Let `M^•` be a cochain complex of an abelian category and let
`a : M^•[0] ⟶ A^{•,•}` be a homotopy equivalence of complexes of complexes.
Then the induced map `α : M^• ⟶ Tot(A^{•,•})` is a homotopy equivalence.
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex

/-- View a complex `M` as a complex of complexes by placing it in (outer)
degree `0`. -/
noncomputable abbrev singleObjComplex
    {V : Type*} [Category V] [Abelian V]
    (M : HomologicalComplex V (ComplexShape.up ℤ)) :
    HomologicalComplex₂ V (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (HomologicalComplex.single
      (HomologicalComplex V (ComplexShape.up ℤ)) (ComplexShape.up ℤ) 0).obj M

/-- The components of the induced map at each inner degree `i`. -/
noncomputable def totalAlphaF
    {V : Type*} [Category V] [Abelian V]
    (M : HomologicalComplex V (ComplexShape.up ℤ))
    (A : HomologicalComplex₂ V (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [A.HasTotal (ComplexShape.up ℤ)]
    (a : (singleObjComplex M) ⟶ A) (i : ℤ) :
    M.X i ⟶ (A.total (ComplexShape.up ℤ)).X i :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv.f i ≫
    (a.f 0).f i ≫
    A.ιTotal (ComplexShape.up ℤ) 0 i i (by simp)

/-- Chain-map compatibility for `totalAlphaF`. -/
lemma totalAlphaF_comm_aux
    {V : Type*} [Category V] [Abelian V]
    (M : HomologicalComplex V (ComplexShape.up ℤ))
    (A : HomologicalComplex₂ V (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [A.HasTotal (ComplexShape.up ℤ)]
    (a : (singleObjComplex M) ⟶ A) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    totalAlphaF M A a i ≫ (A.total (ComplexShape.up ℤ)).d i j =
      M.d i j ≫ totalAlphaF M A a j := by
  obtain rfl : i + 1 = j := hij
  have ha : (a.f 0).f i ≫ (A.d 0 (0 + 1)).f i = 0 := by
    rw [← HomologicalComplex.comp_f, a.comm, single_obj_d, zero_comp, zero_f]
  dsimp [totalAlphaF]
  rw [Category.assoc, Category.assoc, A.ιTotal_d_up_ℤ 0 i i (by simp)]
  simp only [Int.negOnePow_zero, one_smul, Preadditive.comp_add,
    ← Category.assoc, ha, zero_comp, zero_add]
  simp only [Category.assoc]
  rw [(a.f 0).comm_assoc,
    (singleObjXSelf (ComplexShape.up ℤ) 0 M).inv.comm_assoc]

/-- Chain-map compatibility for `totalAlphaF`. -/
alias totalAlphaF_comm := totalAlphaF_comm_aux

/-- The induced chain map. -/
noncomputable def totalAlpha
    {V : Type*} [Category V] [Abelian V]
    (M : HomologicalComplex V (ComplexShape.up ℤ))
    (A : HomologicalComplex₂ V (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [A.HasTotal (ComplexShape.up ℤ)]
    (a : (singleObjComplex M) ⟶ A) :
    M ⟶ A.total (ComplexShape.up ℤ) where
  f i := totalAlphaF M A a i
  comm' i j hij := totalAlphaF_comm M A a i j hij

private lemma singleObjComplex_isZero
    {V : Type*} [Category V] [Abelian V]
    (M : HomologicalComplex V (ComplexShape.up ℤ)) (p q : ℤ) (hp : p ≠ 0) :
    IsZero (((singleObjComplex M).X p).X q) :=
  (HomologicalComplex.eval V (ComplexShape.up ℤ) q).map_isZero
    (isZero_single_obj_X (ComplexShape.up ℤ) 0 M p hp)

private lemma singleObjComplex_hasTotal
    {V : Type*} [Category V] [Abelian V]
    (M : HomologicalComplex V (ComplexShape.up ℤ)) :
    (singleObjComplex M).HasTotal (ComplexShape.up ℤ) := by
  apply HomologicalComplex₂.hasTotal_of_finite
  intro n
  refine (Set.finite_singleton (0, n)).subset ?_
  rintro ⟨p, q⟩ ⟨hpq, hz⟩
  by_cases hp : p = 0
  · have hq : q = n := by simpa [hp] using hpq
    simp [hp, hq]
  · exact (hz (singleObjComplex_isZero M p q hp)).elim

private noncomputable def singleObjComplexTotalDesc
    {V : Type*} [Category V] [Abelian V]
    (M : HomologicalComplex V (ComplexShape.up ℤ))
    [(singleObjComplex M).HasTotal (ComplexShape.up ℤ)] (n : ℤ) :
    ((singleObjComplex M).total (ComplexShape.up ℤ)).X n ⟶ M.X n :=
  (singleObjComplex M).totalDesc (fun p q h =>
    if hp : p = 0 then
      eqToHom (by
        have hq : q = n := by simpa [hp] using h
        subst p q
        rfl) ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 M).hom.f n
    else 0)

private lemma singleObjComplex_unit_isIso
    {V : Type*} [Category V] [Abelian V]
    (M : HomologicalComplex V (ComplexShape.up ℤ))
    [(singleObjComplex M).HasTotal (ComplexShape.up ℤ)] :
    IsIso (totalAlpha M (singleObjComplex M) (𝟙 _)) := by
  have hf (n : ℤ) : IsIso ((totalAlpha M (singleObjComplex M) (𝟙 _)).f n) := by
    have hd : (singleObjComplex M).ιTotal (ComplexShape.up ℤ) 0 n n (by simp) ≫
        singleObjComplexTotalDesc M n = (singleObjXSelf (ComplexShape.up ℤ) 0 M).hom.f n := by
      simp [singleObjComplexTotalDesc]
    refine ⟨singleObjComplexTotalDesc M n, ?_, ?_⟩
    · dsimp [totalAlpha, totalAlphaF]
      rw [Category.id_comp, Category.assoc, hd]
      simpa only [HomologicalComplex.comp_f, id_f] using
        congrArg (fun f => f.f n) (singleObjXSelf (ComplexShape.up ℤ) 0 M).inv_hom_id
    · apply HomologicalComplex₂.total.hom_ext (ComplexShape.up ℤ)
      intro p q h
      by_cases hp : p = 0
      · have hq : q = n := by simpa [hp] using h
        subst p q
        rw [← Category.assoc, hd]
        simp [totalAlpha, totalAlphaF, ← Category.assoc,
          ← HomologicalComplex.comp_f]
      · exact (singleObjComplex_isZero M p q hp).eq_of_src _ _
  exact HomologicalComplex.Hom.isIso_of_components _

private lemma totalAlpha_eq
    {V : Type*} [Category V] [Abelian V]
    (M : HomologicalComplex V (ComplexShape.up ℤ))
    (A : HomologicalComplex₂ V (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [(singleObjComplex M).HasTotal (ComplexShape.up ℤ)]
    [A.HasTotal (ComplexShape.up ℤ)] (a : singleObjComplex M ⟶ A) :
    totalAlpha M A a =
      totalAlpha M (singleObjComplex M) (𝟙 _) ≫
        HomologicalComplex₂.total.map a (ComplexShape.up ℤ) := by
  ext n
  simp [totalAlpha, totalAlphaF, Category.assoc]

/-- Existence of the inverse map `β` together with its homotopy data. -/
lemma totalAlpha_inverse_data
    {V : Type*} [Category V] [Abelian V]
    (M : HomologicalComplex V (ComplexShape.up ℤ))
    (A : HomologicalComplex₂ V (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [A.HasTotal (ComplexShape.up ℤ)]
    (a : HomotopyEquiv (singleObjComplex M) A) :
    ∃ β : A.total (ComplexShape.up ℤ) ⟶ M,
      totalAlpha M A a.hom ≫ β = 𝟙 M ∧
      Nonempty (Homotopy (β ≫ totalAlpha M A a.hom)
                         (𝟙 (A.total (ComplexShape.up ℤ)))) := by
  have := singleObjComplex_hasTotal M
  let u := totalAlpha M (singleObjComplex M) (𝟙 _)
  have : IsIso u := singleObjComplex_unit_isIso M
  have ha : a.hom ≫ a.inv = 𝟙 _ := by
    apply HomologicalComplex.Hom.ext
    funext p
    simpa [dNext, prevD, singleObjComplex] using a.homotopyHomInvId.comm p
  refine ⟨HomologicalComplex₂.total.map a.inv (ComplexShape.up ℤ) ≫ inv u, ?_, ?_⟩
  · rw [totalAlpha_eq, ← Category.assoc, Category.assoc u,
      ← HomologicalComplex₂.total.map_comp, ha, HomologicalComplex₂.total.map_id,
      Category.comp_id, IsIso.hom_inv_id]
  · have h := HomologicalComplex₂.totalMapHomotopy₁ a.homotopyInvHomId (ComplexShape.up ℤ)
    rw [HomologicalComplex₂.total.map_comp, HomologicalComplex₂.total.map_id] at h
    refine ⟨?_⟩
    convert h using 1
    rw [totalAlpha_eq, Category.assoc, ← Category.assoc (inv u),
      IsIso.inv_hom_id, Category.id_comp]

/-- Let `M^•` be a complex of an abelian category and `A^{•,•}` a complex of
complexes. If `a : M^•[0] ⟶ A^{•,•}` is part of a homotopy equivalence in the
category of complexes of complexes, then the canonical induced map
`α : M^• ⟶ Tot(A^{•,•})` is a homotopy equivalence. -/
@[stacks 0FKH]
theorem isHomotopyEquiv_total_of_isHomotopyEquiv
    {V : Type*} [Category V] [Abelian V]
    (M : HomologicalComplex V (ComplexShape.up ℤ))
    (A : HomologicalComplex₂ V (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [A.HasTotal (ComplexShape.up ℤ)]
    (a : HomotopyEquiv (singleObjComplex M) A) :
    Nonempty {e : HomotopyEquiv M (A.total (ComplexShape.up ℤ)) //
        e.hom = totalAlpha M A a.hom} := by
  obtain ⟨β, hβ, ⟨h⟩⟩ := totalAlpha_inverse_data M A a
  exact ⟨⟨⟨totalAlpha M A a.hom, β, Homotopy.ofEq hβ, h⟩, rfl⟩⟩

end
