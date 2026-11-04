module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.HomEquiv
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Category.Preorder
public import StacksFrontier.Algebra.Homology.StupidTruncation
public import StacksFrontier.Algebra.Homology.TotalSingleRow
public import StacksFrontier.CategoryTheory.Triangulated.OperationsOnFullSubcategories
public import StacksFrontier.Homology.KFlat.Bifunctor
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Bounded complexes and bifunctor-relative K-flatness

Let `F : A ⥤ B ⥤ D` be a bifunctor which is additive in each variable, with `D` abelian, and
let `KFlat F` be the K-flatness of `CochainComplex.KFlatBifunctor`: a complex `K` of objects
of `B` is K-flat when `Tot(F(G, K))` is acyclic for every acyclic complex `G` of objects of
`A`.  On a ringed site, with `F = ⊗_O`, this is Stacks Tag 06YN.

This module is the engine of Stacks Tag 06YQ: a bounded above complex of flat `O`-modules is
K-flat.  It proves, for an arbitrary such bifunctor, that a complex strictly bounded on both
sides is K-flat as soon as each of its terms is (placed in its own degree); that a single
object placed in one degree is K-flat as soon as `F(-, M)` preserves acyclicity, which for
`F = ⊗_O` is the flatness of `M`; and that K-flatness passes to a colimit, whence the passage
from bounded to bounded above.

## Main results

* `CochainComplex.KFlatBifunctor.KFlat.of_iso`: K-flatness transports along an isomorphism
  of complexes.
* `CochainComplex.KFlatBifunctor.kFlat_X₁_of_degreewiseSplit`,
  `CochainComplex.KFlatBifunctor.kFlat_X₂_of_degreewiseSplit`,
  `CochainComplex.KFlatBifunctor.kFlat_X₃_of_degreewiseSplit`: the two-out-of-three property
  of K-flatness in a degreewise split short exact sequence of complexes, one implication per
  vertex.
* `CochainComplex.KFlatBifunctor.kFlat_single_of_exact`: **the base case** — an object `M` of
  `B` placed in a degree `q` gives a K-flat complex as soon as `F(-, M)` carries acyclic
  complexes to acyclic complexes.
* `CochainComplex.KFlatBifunctor.kFlat_of_kFlat_single_top`: a complex which is strictly
  bounded above by `b` is K-flat as soon as its top term, placed in degree `b`, and its
  stupid truncation in degrees `≤ b - 1` are.
* `CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE_of_isStrictlyGE`: a complex which is
  strictly bounded on both sides is K-flat as soon as each of its terms, placed in its own
  degree, is.
* `CochainComplex.KFlatBifunctor.kFlat_of_isColimit`: **K-flatness is stable under colimits**,
  given that `F` commutes with them in the second variable and that they are exact in `D`.
* `CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE`: **the engine completed** — a complex
  which is strictly bounded above is K-flat as soon as each of its terms, placed in its own
  degree, is.

## Implementation notes

The two-out-of-three property is available in `StacksFrontier.Homology.KFlat.Bifunctor` for a
distinguished triangle of the homotopy category `K(B)` (Stacks Tag 07A3).  Every induction
over the length of a complex produces instead a *degreewise split short exact sequence* of
complexes, so the three statements here are the form in which that property is actually
applied; their proof is Mathlib's
`CochainComplex.trianglehOfDegreewiseSplit_distinguished`, which turns such a sequence into
a distinguished triangle of `K(B)`.  No exactness of `F` is used, and `B` is not assumed
abelian: binary biproducts and a zero object are what the splitting and the triangle need.

The splitting used by the induction is the tautological one: for `L` strictly bounded above
by `b`, the top term `L^b` placed in degree `b` includes into `L`
(`HomologicalComplex.mkHomFromSingle`), the quotient is the stupid truncation
`L.stupidTrunc (embeddingUpIntLE (b - 1))` (`ComplexShape.Embedding.liftExtend`), and in
each degree one of the two legs is an isomorphism while the opposite object vanishes, which
is where the degreewise splitting comes from.  The induction then runs on `b - a` with the
stupid truncation as the inductive step, and terminates on a complex concentrated in a
single degree, which is isomorphic to that term placed in that degree.  The case `b < a`,
where the complex vanishes, is handled by replacing the lower bound by `b`: that is why no
separate statement that a zero complex is K-flat is needed, and none is proved — the
induced bifunctor on complexes `F.map₂HomologicalComplex` carries no
`PreservesZeroMorphisms` instance at this Mathlib pin, so such a statement would have to
construct one.  The passage to a bounded above complex does not need one either: the tower
`σ^{≥ b - m}K` is indexed so that its term at `m` has length exactly `m`, never zero.

The base case rests on the identification of the total complex of a double complex
concentrated in one row with the corresponding shift of that row
(`StacksDraft.TotalSingleRow.totalSingleRowUnit`): the double complex `F(Gᵖ, (M[q])ʳ)` is
concentrated in the row `q`, where it is `F(G, M)` (`mapBifunctorSingleIso`, whose squares
commute by `StacksDraft.TotalSingleRow.singleMapHomologicalComplex_naturality`).

The source reduces the *acyclic* factor to a bounded above complex and invokes the first
spectral sequence of a double complex (Homology, Lemma 0132), machinery which Mathlib does
not have.  The route here filters the *K-flat* factor from below instead, by the stupid
truncations `σ^{≥ b - m}K` of `StacksDraft.StupidTruncation.stupidTruncTower`: in each degree
that tower is zero up to a point and then constant, so `K` is its colimit
(`isColimit_truncCocone`, via `isColimit_of_eventually_isIso`), and K-flatness passes to a
colimit as soon as `Tot(F(G, -))` commutes with it and it is exact in `D`.  The first of these
is `preservesColimitsOfShape_totalFunctor`, whose per-total-degree core
`preservesColimit_totalFunctor_eval` says that a coproduct of colimits is a colimit of
coproducts; no finiteness of the antidiagonal is needed.  The second is taken as the
hypothesis `hexact`.  Both hold for `F = ⊗_O` on a ringed site, the first because `Mod(O)` is
monoidal closed and the second because it satisfies AB5 (Stacks Tag 03DB); that is how they are
discharged in `colim_of_system_KFlat_isKFlat`, the tagged form of Stacks Tag 06YR.

## References

* [The Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [The Stacks Project, Tag 07A3](https://stacks.math.columbia.edu/tag/07A3)
-/

open CategoryTheory CategoryTheory.Limits Pretriangulated
open ComplexShape HomologicalComplex

noncomputable section

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Preadditive A] [Preadditive B] [HasZeroObject B] [HasBinaryBiproducts B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]

omit [HasZeroObject B] [HasBinaryBiproducts B] in
/-- K-flatness is invariant under isomorphism of complexes. -/
theorem KFlat.of_iso {K K' : CochainComplex B ℤ} (hK : KFlat F K) (e : K ≅ K') :
    KFlat F K' := fun G hG n =>
  HomologicalComplex.ExactAt.of_iso (hK G hG n)
    (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)).obj G).mapIso e)

/-- Two out of three in a degreewise split short exact sequence of complexes: the middle
term is K-flat as soon as the two outer ones are. -/
theorem kFlat_X₂_of_degreewiseSplit (S : ShortComplex (CochainComplex B ℤ))
    (σ : ∀ n, (S.map (HomologicalComplex.eval B _ n)).Splitting)
    (h₁ : KFlat F S.X₁) (h₃ : KFlat F S.X₃) : KFlat F S.X₂ :=
  kFlat_obj₂_of_distTriang F _ _ _
    (CochainComplex.trianglehOfDegreewiseSplit_distinguished S σ) h₁ h₃

/-- Two out of three in a degreewise split short exact sequence of complexes: the first
term is K-flat as soon as the other two are. -/
theorem kFlat_X₁_of_degreewiseSplit (S : ShortComplex (CochainComplex B ℤ))
    (σ : ∀ n, (S.map (HomologicalComplex.eval B _ n)).Splitting)
    (h₂ : KFlat F S.X₂) (h₃ : KFlat F S.X₃) : KFlat F S.X₁ :=
  kFlat_obj₁_of_distTriang F _ _ _
    (CochainComplex.trianglehOfDegreewiseSplit_distinguished S σ) h₂ h₃

/-- Two out of three in a degreewise split short exact sequence of complexes: the last
term is K-flat as soon as the other two are. -/
theorem kFlat_X₃_of_degreewiseSplit (S : ShortComplex (CochainComplex B ℤ))
    (σ : ∀ n, (S.map (HomologicalComplex.eval B _ n)).Splitting)
    (h₁ : KFlat F S.X₁) (h₂ : KFlat F S.X₂) : KFlat F S.X₃ :=
  kFlat_obj₃_of_distTriang F _ _ _
    (CochainComplex.trianglehOfDegreewiseSplit_distinguished S σ) h₁ h₂

section Single

/-- The complex `p ↦ F(Gᵖ, M)`.  It is `((F.flip.obj M).mapHomologicalComplex _).obj G`,
written out so as not to carry the additivity of `F.flip.obj M` as an instance, and it is the
row `q` of the double complex attached to `G` and to `M` placed in the degree `q`. -/
noncomputable def rowComplex (G : CochainComplex A ℤ) (M : B) : CochainComplex D ℤ where
  X p := (F.obj (G.X p)).obj M
  d p p' := (F.map (G.d p p')).app M
  shape p p' h := by rw [G.shape p p' h, F.map_zero, zero_app]
  d_comp_d' p p' p'' _ _ := by
    rw [← NatTrans.comp_app, ← F.map_comp, G.d_comp_d, F.map_zero, zero_app]

/-- **The double complex of a complex concentrated in one degree is concentrated in one row.**
Applying `F` to `G` and to `M` placed in the degree `q` gives the double complex
`(p, r) ↦ F(Gᵖ, (M[q])ʳ)`, which vanishes for `r ≠ q` and whose row `q` is `F(G, M)`.  In each
first degree `p` this is `HomologicalComplex.singleMapHomologicalComplex` for the functor
`F(Gᵖ, -)`, and the squares commute by naturality of `F` in the first variable. -/
noncomputable def mapBifunctorSingleIso (G : CochainComplex A ℤ) (M : B) (q : ℤ) :
    ((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj G).obj
        ((single B (ComplexShape.up ℤ) q).obj M) ≅
      StacksDraft.TotalSingleRow.singleRow (rowComplex F G M) q :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (HomologicalComplex.singleMapHomologicalComplex (F.obj (G.X p))
      (ComplexShape.up ℤ) q).app M)
    (fun p p' _ => StacksDraft.TotalSingleRow.singleMapHomologicalComplex_naturality
      (F.map (G.d p p')) q M)

omit [HasBinaryBiproducts B] in
/-- **The base case of Stacks 06YQ.**  An object `M` of `B` placed in a degree `q` gives a
complex which is K-flat for `F` as soon as `F(-, M)` carries acyclic complexes to acyclic
complexes.  Indeed `Tot(F(G, M[q]))` is the shift by `-q` of `F(G, M)`: the double complex is
concentrated in the row `q` by `mapBifunctorSingleIso`, and the total complex of a double
complex concentrated in one row is the corresponding shift of that row, by
`StacksDraft.TotalSingleRow.totalSingleRowUnit`.  For `F = ⊗_O` on a ringed site the hypothesis
is the flatness of the `O`-module `M`. -/
theorem kFlat_single_of_exact (M : B) (q : ℤ)
    (h : ∀ G : CochainComplex A ℤ, G.Acyclic → (rowComplex F G M).Acyclic) :
    KFlat F ((single B (ComplexShape.up ℤ) q).obj M) := by
  intro G hG
  have e := mapBifunctorSingleIso F G M q
  have : (StacksDraft.TotalSingleRow.singleRow (rowComplex F G M) q).HasTotal
      (ComplexShape.up ℤ) := HomologicalComplex₂.hasTotal_of_iso e _
  have hac := StacksDraft.TotalSingleRow.acyclic_total_singleRow (rowComplex F G M) q (h G hG)
  have etot :
      (((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj G).obj
          ((single B (ComplexShape.up ℤ) q).obj M)).total (ComplexShape.up ℤ) ≅
        (StacksDraft.TotalSingleRow.singleRow (rowComplex F G M) q).total
          (ComplexShape.up ℤ) :=
    { hom := HomologicalComplex₂.total.map e.hom (ComplexShape.up ℤ)
      inv := HomologicalComplex₂.total.map e.inv (ComplexShape.up ℤ)
      hom_inv_id := by
        rw [← HomologicalComplex₂.total.map_comp, e.hom_inv_id,
          HomologicalComplex₂.total.map_id]
      inv_hom_id := by
        rw [← HomologicalComplex₂.total.map_comp, e.inv_hom_id,
          HomologicalComplex₂.total.map_id] }
  intro n
  exact HomologicalComplex.ExactAt.of_iso (hac n) etot.symm

end Single

section Bounded

variable (L : CochainComplex B ℤ) (b : ℤ)

omit [HasZeroObject B] [HasBinaryBiproducts B] in
private lemma comp_d_eq_zero_of_isStrictlyLE [L.IsStrictlyLE b] :
    ∀ k, (ComplexShape.up ℤ).Rel b k → (𝟙 (L.X b)) ≫ L.d b k = 0 := by
  intro k hk
  simp only [ComplexShape.up_Rel] at hk
  exact (L.isZero_of_isStrictlyLE b k (by omega)).eq_of_tgt _ _

/-- The inclusion of the top term of `L` is an isomorphism in degree `b`. -/
private lemma isIso_mkHomFromSingle_f_top {C : Type*} [Category C] [Preadditive C]
    [HasZeroObject C] (L : CochainComplex C ℤ) (b : ℤ) [L.IsStrictlyLE b] :
    IsIso ((mkHomFromSingle (𝟙 (L.X b)) (comp_d_eq_zero_of_isStrictlyLE L b)).f b) := by
  rw [mkHomFromSingle_f, Category.comp_id]
  infer_instance

/-- The stupid truncation of `L` in degrees `≤ b - 1` vanishes in degrees `> b - 1`. -/
private lemma isZero_stupidTrunc_X_of_gt {C : Type*} [Category C] [Preadditive C]
    [HasZeroObject C] (L : CochainComplex C ℤ) (b q : ℤ) (hq : b - 1 < q) :
    IsZero ((L.stupidTrunc (embeddingUpIntLE (b - 1))).X q) :=
  L.isZero_stupidTrunc_X _ q (fun k => by change (b - 1 : ℤ) - (k : ℤ) ≠ q; omega)

/-- A complex concentrated in the single degree `b` is isomorphic to its term in degree `b`
placed in degree `b`. -/
private def isoSingleOfConcentrated [L.IsStrictlyLE b] [L.IsStrictlyGE b] :
    (single B (ComplexShape.up ℤ) b).obj (L.X b) ≅ L := by
  haveI : ∀ i : ℤ,
      IsIso ((mkHomFromSingle (𝟙 (L.X b)) (comp_d_eq_zero_of_isStrictlyLE L b)).f i) := by
    intro i
    by_cases hi : i = b
    · subst hi
      exact isIso_mkHomFromSingle_f_top L i
    · refine (isZero_single_obj_X (ComplexShape.up ℤ) b (L.X b) i hi).isIso ?_ _
      rcases lt_or_gt_of_ne hi with h | h
      · exact L.isZero_of_isStrictlyGE b i h
      · exact L.isZero_of_isStrictlyLE b i h
  haveI := HomologicalComplex.Hom.isIso_of_components
    (mkHomFromSingle (𝟙 (L.X b)) (comp_d_eq_zero_of_isStrictlyLE L b))
  exact asIso (mkHomFromSingle (𝟙 (L.X b)) (comp_d_eq_zero_of_isStrictlyLE L b))

/-- Splitting off the top term of a complex which is strictly bounded above: the complex is
K-flat as soon as its top term, placed in degree `b`, and its stupid truncation in degrees
`≤ b - 1` are.  The two sit in a degreewise split short exact sequence with the complex, so
the two-out-of-three property applies. -/
theorem kFlat_of_kFlat_single_top [L.IsStrictlyLE b]
    (htop : KFlat F ((single B (ComplexShape.up ℤ) b).obj (L.X b)))
    (hrest : KFlat F (L.stupidTrunc (embeddingUpIntLE (b - 1)))) :
    KFlat F L := by
  set e := embeddingUpIntLE (b - 1) with he
  set ι := mkHomFromSingle (𝟙 (L.X b)) (comp_d_eq_zero_of_isStrictlyLE L b) with hιdef
  have hιb : IsIso (ι.f b) := isIso_mkHomFromSingle_f_top L b
  have hlift : e.HasLift (𝟙 (L.restriction e)) :=
    fun _ hj _ _ => (hj.false_of_isTruncLE).elim
  set π := e.liftExtend (𝟙 (L.restriction e)) hlift with hπdef
  have hπiso : ∀ i : ℤ, i ≠ b → IsIso (π.f i) := by
    intro i hi
    by_cases hib : i ≤ b - 1
    · refine (e.isIso_liftExtend_f_iff _ hlift
        (DerivedCategory.embeddingUpIntLE_f_toNat (b - 1) i hib)).2 ?_
      rw [HomologicalComplex.id_f]
      infer_instance
    · exact (L.isZero_of_isStrictlyLE b i (by omega)).isIso
        (isZero_stupidTrunc_X_of_gt L b i (by omega)) _
  have hTb : IsZero ((L.stupidTrunc e).X b) := isZero_stupidTrunc_X_of_gt L b b (by omega)
  have hcomp : ι ≫ π = 0 := HomologicalComplex.hom_ext _ _ fun i => by
    by_cases hi : i = b
    · subst hi; exact hTb.eq_of_tgt _ _
    · exact (isZero_single_obj_X (ComplexShape.up ℤ) b (L.X b) i hi).eq_of_src _ _
  refine kFlat_X₂_of_degreewiseSplit F (ShortComplex.mk ι π hcomp) (fun n => ?_) htop hrest
  by_cases hn : n = b
  · subst hn
    have := hιb
    exact { r := inv (ι.f n)
            s := 0
            f_r := by simp
            s_g := hTb.eq_of_tgt _ _
            id := by simp }
  · have := hπiso n hn
    exact { r := 0
            s := inv (π.f n)
            f_r := (isZero_single_obj_X (ComplexShape.up ℤ) b (L.X b) n hn).eq_of_src _ _
            s_g := by simp
            id := by simp }

private lemma kFlat_of_bounds (n : ℕ) : ∀ (L : CochainComplex B ℤ) (a b : ℤ),
    L.IsStrictlyLE b → L.IsStrictlyGE a → a + n = b →
    (∀ q : ℤ, a ≤ q → q ≤ b →
      KFlat F ((single B (ComplexShape.up ℤ) q).obj (L.X q))) → KFlat F L := by
  induction n with
  | zero =>
      intro L a b hle hge hab hterm
      obtain rfl : a = b := by omega
      exact ((hterm a le_rfl le_rfl).of_iso F (isoSingleOfConcentrated L a))
  | succ n IH =>
      intro L a b hle hge hab hterm
      set e := embeddingUpIntLE (b - 1) with he
      have hiso : ∀ q : ℤ, q ≤ b - 1 → ((L.stupidTrunc e).X q ≅ L.X q) := fun q hq =>
        L.stupidTruncXIso e (DerivedCategory.embeddingUpIntLE_f_toNat (b - 1) q hq)
      have hgeT : CochainComplex.IsStrictlyGE (L.stupidTrunc e) a := by
        refine IsStrictlySupported.mk (fun i hi => ?_)
        rw [notMem_range_embeddingUpIntGE_iff] at hi
        by_cases hib : i ≤ b - 1
        · exact IsZero.of_iso (L.isZero_of_isStrictlyGE a i hi) (hiso i hib)
        · exact isZero_stupidTrunc_X_of_gt L b i (by omega)
      refine kFlat_of_kFlat_single_top F L b (hterm b (by omega) le_rfl)
        (IH _ a (b - 1) inferInstance hgeT (by omega) (fun q hq hq' => ?_))
      exact (hterm q hq (by omega)).of_iso F
        ((single B (ComplexShape.up ℤ) q).mapIso (hiso q hq').symm)

/-- **The engine of Stacks 06YQ.**  A complex which is strictly bounded on both sides is
K-flat as soon as each of its terms, placed in its own degree, gives a K-flat complex.
The proof is an induction on the length of the complex, splitting off the top term by the
degreewise split short exact sequence attached to its stupid truncations. -/
theorem kFlat_of_isStrictlyLE_of_isStrictlyGE (a : ℤ) [L.IsStrictlyLE b] [L.IsStrictlyGE a]
    (hterm : ∀ q : ℤ, KFlat F ((single B (ComplexShape.up ℤ) q).obj (L.X q))) :
    KFlat F L := by
  by_cases hab : a ≤ b
  · exact kFlat_of_bounds F (b - a).toNat L a b inferInstance inferInstance (by omega)
      (fun q _ _ => hterm q)
  · have hge : L.IsStrictlyGE b := by
      refine IsStrictlySupported.mk (fun i hi => ?_)
      rw [notMem_range_embeddingUpIntGE_iff] at hi
      by_cases h : i < a
      · exact L.isZero_of_isStrictlyGE a i h
      · exact L.isZero_of_isStrictlyLE b i (by omega)
    exact kFlat_of_bounds F 0 L b b inferInstance hge (by omega) (fun q _ _ => hterm q)

end Bounded

section Colimit

omit [Preadditive A] [HasZeroObject B] [HasBinaryBiproducts B] [Abelian D] in
/-- A cocone over a diagram indexed by a preorder is a colimit as soon as its leg is an
isomorphism at every index above some `j₀` and the diagram vanishes at every other index.
This is the shape of the presentation of a bounded above complex as the colimit of its stupid
truncations: in each degree that tower is zero up to a point and constant afterwards. -/
noncomputable def isColimit_of_eventually_isIso {E J : Type*} [Category E] [Preorder J]
    {Dg : J ⥤ E} (c : Cocone Dg) (j₀ : J) (hiso : ∀ j, j₀ ≤ j → IsIso (c.ι.app j))
    (hzero : ∀ j, ¬ j₀ ≤ j → IsZero (Dg.obj j)) :
    IsColimit c where
  desc s := haveI := hiso j₀ le_rfl; inv (c.ι.app j₀) ≫ s.ι.app j₀
  fac s j := by
    have := hiso j₀ le_rfl
    by_cases hj : j₀ ≤ j
    · have := hiso j hj
      have hw : Dg.map (homOfLE hj) ≫ c.ι.app j = c.ι.app j₀ := c.w _
      have hws : Dg.map (homOfLE hj) ≫ s.ι.app j = s.ι.app j₀ := s.w _
      have : IsIso (Dg.map (homOfLE hj)) := by
        have he : Dg.map (homOfLE hj) = c.ι.app j₀ ≫ inv (c.ι.app j) := by
          rw [← hw, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
        rw [he]
        infer_instance
      have h1 : Dg.map (homOfLE hj) ≫ c.ι.app j ≫ inv (c.ι.app j₀) = 𝟙 _ := by
        rw [← Category.assoc, hw, IsIso.hom_inv_id]
      rw [← Category.assoc, ← IsIso.inv_eq_of_hom_inv_id h1, ← hws, IsIso.inv_hom_id_assoc]
    · exact (hzero j hj).eq_of_src _ _
  uniq s m hm := by
    have := hiso j₀ le_rfl
    rw [← hm j₀, IsIso.inv_hom_id_assoc]

/-! The total complex of a double complex of objects of `D` is formed degreewise from the
coproducts of the terms `Z^{p,r}` along the antidiagonals `p + r = n`, each of them indexed by
a *fibre of the addition of integers*, hence by a type in `Type 0`. So what the statements of
this section need of `D` beyond the colimits of shape `J` they are about is only that those
antidiagonal coproducts exist, which is what `HasTotal` records. Asking instead for
`HasColimits D`, as this section once did, ties the shapes available in `D` to the universe of
`D`'s own morphisms: on a ringed site that universe is the maximum of the object universe of
the site and the module universe, so `HasColimits (Mod O)` is a genuine size condition which a
site whose objects live above its modules does not satisfy, while the `Type 0` colimits the
total complex needs are there at every pair of universes.

A consumer in which `D` has all colimits still gets the hypothesis by synthesis. One in which
`D` is a concrete category can hit the one awkwardness of the telescoped form — instance
search solves `K.HasTotal c` for a fixed `K` but not always the `∀ K` goal — and should then
pass `fun _ ↦ inferInstance`. -/
variable [∀ K : HomologicalComplex₂ D (ComplexShape.up ℤ) (ComplexShape.up ℤ),
    K.HasTotal (ComplexShape.up ℤ)]
  {J : Type*} [Category J] [HasColimitsOfShape J B] [HasColimitsOfShape J D]

omit [HasZeroObject B] [HasBinaryBiproducts B] [HasColimitsOfShape J D]
  [∀ K : HomologicalComplex₂ D (ComplexShape.up ℤ) (ComplexShape.up ℤ),
      K.HasTotal (ComplexShape.up ℤ)]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)] in
/-- An additive functor which preserves colimits of shape `J` induces a functor on cochain
complexes which preserves them too, colimits of complexes being computed degreewise. -/
theorem preservesColimitsOfShape_mapHomologicalComplex (Φ : B ⥤ D) [Φ.Additive]
    [PreservesColimitsOfShape J Φ] :
    PreservesColimitsOfShape J (Φ.mapHomologicalComplex (ComplexShape.up ℤ)) where
  preservesColimit :=
    { preserves := fun {_s} hs => ⟨HomologicalComplex.isColimitOfEval _ _ (fun r =>
        isColimitOfPreserves (HomologicalComplex.eval B (ComplexShape.up ℤ) r ⋙ Φ) hs)⟩ }

omit [HasZeroObject B] [HasBinaryBiproducts B] [HasColimitsOfShape J D]
  [∀ K : HomologicalComplex₂ D (ComplexShape.up ℤ) (ComplexShape.up ℤ),
      K.HasTotal (ComplexShape.up ℤ)]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)] in
/-- The double-complex-valued functor `K ↦ F(G, K)` preserves colimits of shape `J` as soon as
each `F(X, -)` does: colimits of double complexes are computed in each first degree `p`, where
the functor is `F(Gᵖ, -)` applied termwise. -/
theorem preservesColimitsOfShape_mapBifunctorObj (G : CochainComplex A ℤ)
    (hF : ∀ X : A, PreservesColimitsOfShape J (F.obj X)) :
    PreservesColimitsOfShape J
      ((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj G) where
  preservesColimit :=
    { preserves := fun {_s} hs => ⟨HomologicalComplex.isColimitOfEval _ _ (fun p => by
        have := hF (G.X p)
        have := preservesColimitsOfShape_mapHomologicalComplex (J := J) (F.obj (G.X p))
        exact isColimitOfPreserves
          ((F.obj (G.X p)).mapHomologicalComplex (ComplexShape.up ℤ)) hs)⟩ }

omit [Preadditive A] [Preadditive B] [HasZeroObject B] [HasBinaryBiproducts B]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)] in
/-- **Per-total-degree colimit preservation.**  In each total degree `Tot(Z)ⁿ` is the coproduct
of the terms `Z^{p,r}` with `p + r = n`, so the functor `Z ↦ Tot(Z)ⁿ` is the coproduct over that
fixed antidiagonal of the bidegree evaluations.  Each bidegree evaluation preserves colimits of
shape `J` — colimits of complexes are computed degreewise — and a coproduct of colimits is a
colimit of coproducts, which is what the three fields below check against the universal
property of `HomologicalComplex₂.totalDesc`.  No finiteness of the antidiagonal is needed. -/
theorem preservesColimit_totalFunctor_eval
    (E : J ⥤ HomologicalComplex₂ D (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (n : ℤ) :
    PreservesColimit E
      (HomologicalComplex₂.totalFunctor D (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ⋙ HomologicalComplex.eval D (ComplexShape.up ℤ) n) where
  preserves {s} hs := by
    have hev : ∀ p r : ℤ, IsColimit
        ((HomologicalComplex.eval (HomologicalComplex D (ComplexShape.up ℤ))
            (ComplexShape.up ℤ) p ⋙
          HomologicalComplex.eval D (ComplexShape.up ℤ) r).mapCocone s) :=
      fun p r => isColimitOfPreserves _ hs
    have hmc : ∀ j : J,
        ((HomologicalComplex₂.totalFunctor D (ComplexShape.up ℤ) (ComplexShape.up ℤ)
              (ComplexShape.up ℤ) ⋙
            HomologicalComplex.eval D (ComplexShape.up ℤ) n).mapCocone s).ι.app j =
          (HomologicalComplex₂.total.map (s.ι.app j) (ComplexShape.up ℤ)).f n := fun _ => rfl
    let cone : ∀ (t : Cocone (E ⋙ (HomologicalComplex₂.totalFunctor D (ComplexShape.up ℤ)
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
          HomologicalComplex.eval D (ComplexShape.up ℤ) n))) (p r : ℤ)
        (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (p, r) = n),
        Cocone (E ⋙ (HomologicalComplex.eval (HomologicalComplex D (ComplexShape.up ℤ))
            (ComplexShape.up ℤ) p ⋙
          HomologicalComplex.eval D (ComplexShape.up ℤ) r)) := fun t p r h =>
      { pt := t.pt
        ι :=
          { app := fun j => (E.obj j).ιTotal (ComplexShape.up ℤ) p r n h ≫ t.ι.app j
            naturality := fun j j' g => by
              have htw : (HomologicalComplex₂.total.map (E.map g) (ComplexShape.up ℤ)).f n ≫
                  t.ι.app j' = t.ι.app j := t.w g
              have key : ∀ k : ((E.obj j').total (ComplexShape.up ℤ)).X n ⟶ t.pt,
                  ((E.map g).f p).f r ≫
                      (E.obj j').ιTotal (ComplexShape.up ℤ) p r n h ≫ k =
                    (E.obj j).ιTotal (ComplexShape.up ℤ) p r n h ≫
                      (HomologicalComplex₂.total.map (E.map g) (ComplexShape.up ℤ)).f n ≫ k :=
                fun k => by rw [← HomologicalComplex₂.ιTotal_map_assoc]
              have h1 := key (t.ι.app j')
              rw [htw] at h1
              simpa only [Functor.comp_map, Functor.comp_obj, HomologicalComplex.eval_map,
                Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] using h1 } }
    refine ⟨{ desc := fun t => s.pt.totalDesc (fun p r h => (hev p r).desc (cone t p r h))
              fac := fun t j => ?_
              uniq := fun t m hm => ?_ }⟩
    · refine HomologicalComplex₂.total.hom_ext (ComplexShape.up ℤ) (fun p r hpr => ?_)
      have h2 : s.pt.ιTotal (ComplexShape.up ℤ) p r n hpr ≫
            s.pt.totalDesc (fun p r h => (hev p r).desc (cone t p r h)) =
          (hev p r).desc (cone t p r hpr) := HomologicalComplex₂.ι_totalDesc _ _ _ _ _
      refine Eq.trans (HomologicalComplex₂.ιTotal_map_assoc (E.obj j) s.pt (s.ι.app j)
        (ComplexShape.up ℤ) p r n hpr _) ?_
      exact Eq.trans (congrArg (fun x => ((s.ι.app j).f p).f r ≫ x) h2)
        ((hev p r).fac (cone t p r hpr) j)
    · refine HomologicalComplex₂.total.hom_ext (ComplexShape.up ℤ) (fun p r hpr => ?_)
      have h2 : s.pt.ιTotal (ComplexShape.up ℤ) p r n hpr ≫
            s.pt.totalDesc (fun p r h => (hev p r).desc (cone t p r h)) =
          (hev p r).desc (cone t p r hpr) := HomologicalComplex₂.ι_totalDesc _ _ _ _ _
      refine Eq.trans ?_ h2.symm
      refine (hev p r).hom_ext (fun j => ?_)
      refine Eq.trans ?_ ((hev p r).fac (cone t p r hpr) j).symm
      exact Eq.trans (HomologicalComplex₂.ιTotal_map_assoc (E.obj j) s.pt (s.ι.app j)
        (ComplexShape.up ℤ) p r n hpr m).symm
        (congrArg (fun x => (E.obj j).ιTotal (ComplexShape.up ℤ) p r n hpr ≫ x) (hm j))

omit [Preadditive A] [Preadditive B] [HasZeroObject B] [HasBinaryBiproducts B] in
/-- The total-complex functor preserves colimits of shape `J`: degreewise this is
`preservesColimit_totalFunctor_eval`. -/
theorem preservesColimitsOfShape_totalFunctor :
    PreservesColimitsOfShape J
      (HomologicalComplex₂.totalFunctor D (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)) where
  preservesColimit {E} :=
    { preserves := fun {_s} hs => ⟨HomologicalComplex.isColimitOfEval _ _ (fun n => by
        have := preservesColimit_totalFunctor_eval (D := D) E n
        exact isColimitOfPreserves
          (HomologicalComplex₂.totalFunctor D (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ) ⋙ HomologicalComplex.eval D (ComplexShape.up ℤ) n) hs)⟩ }

omit [HasZeroObject B] [HasBinaryBiproducts B] in
/-- `Tot(F(G, -))` as a functor on cochain complexes. -/
noncomputable def totFunctor (G : CochainComplex A ℤ) :
    CochainComplex B ℤ ⥤ CochainComplex D ℤ :=
  (F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj G ⋙
    HomologicalComplex₂.totalFunctor D (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)

omit [HasZeroObject B] [HasBinaryBiproducts B]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)] in
/-- `totFunctor F G` sends `K` to the total complex `Tot(F(G, K))`, by definition. -/
lemma totFunctor_obj (G : CochainComplex A ℤ) (K : CochainComplex B ℤ) :
    (totFunctor F G).obj K = totalComplex F G K := rfl

omit [HasZeroObject B] [HasBinaryBiproducts B]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)] in
/-- **K-flatness is stable under colimits** (Stacks Tag 06YR, for a general bifunctor and a
general shape).  The vertex of a colimit cocone over a diagram of K-flat complexes is K-flat,
given that `F` commutes with colimits of that shape in the second variable and that colimits of
that shape are exact in `D`.  Both hold for `F = ⊗_O` on a ringed site and a filtered shape:
the first because `Mod(O)` is monoidal closed, the second because `Mod(O)` satisfies AB5
(Stacks Tag 03DB).

The same statement for the predicate `IsKFlat` of sheaves of `O`-modules is
`colim_of_system_KFlat_isKFlat_of_bifunctor`, whose specialisation to `F = ⊗_O` and the shape
`ℕ` — with both hypotheses discharged — is `colim_of_system_KFlat_isKFlat`, the tagged form of
Stacks Tag 06YR.  It is restated here for `KFlat` because the induction of this file runs over
a bifunctor between three arbitrary additive categories, of which `⊗_O` on `Mod(O)` is one
case. -/
theorem kFlat_of_isColimit {Dg : J ⥤ CochainComplex B ℤ} (c : Cocone Dg) (hc : IsColimit c)
    (hF : ∀ X : A, PreservesColimitsOfShape J (F.obj X))
    (hexact : ∀ (E : J ⥤ CochainComplex D ℤ) (s : Cocone E), IsColimit s →
      (∀ i, (E.obj i).Acyclic) → s.pt.Acyclic)
    (hDg : ∀ i, KFlat F (Dg.obj i)) : KFlat F c.pt := by
  intro G hG
  have : PreservesColimitsOfShape J (totFunctor F G) := by
    have := preservesColimitsOfShape_mapBifunctorObj (J := J) F G hF
    have := preservesColimitsOfShape_totalFunctor (D := D) (J := J)
    exact comp_preservesColimitsOfShape _ _
  exact hexact (Dg ⋙ totFunctor F G) _ (isColimitOfPreserves (totFunctor F G) hc)
    (fun i => hDg i G hG)

end Colimit

section BoundedAbove

variable [∀ K : HomologicalComplex₂ D (ComplexShape.up ℤ) (ComplexShape.up ℤ),
    K.HasTotal (ComplexShape.up ℤ)]
  [HasColimitsOfShape ℕ B] [HasColimitsOfShape ℕ D]

/-- The tower of stupid truncations `σ^{≥ b - m}K` of `K`, indexed by `ℕ`: it is the tower
`StacksDraft.StupidTruncation.stupidTruncTower` reindexed so that the term at `m` is strictly
bounded below by `b - m`, hence — for `K` strictly bounded above by `b` — bounded on both
sides with length `m`. -/
@[ega "0 11.5.1"]
noncomputable def truncDiagram (K : CochainComplex B ℤ) (b : ℤ) :
    ℕ ⥤ CochainComplex B ℤ :=
  (Monotone.functor (f := fun m : ℕ => (m : ℤ) - b)
      (fun _ _ h => by simpa using Int.ofNat_le.2 h)) ⋙
    StacksDraft.StupidTruncation.stupidTruncTower K

/-- The cocone on `truncDiagram K b` with vertex `K`, given by the inclusions of the stupid
truncations.  It is a colimit cocone; see `isColimit_truncCocone`. -/
noncomputable def truncCocone (K : CochainComplex B ℤ) (b : ℤ) :
    Cocone (truncDiagram K b) where
  pt := K
  ι :=
    { app := fun m => HomologicalComplex.ιStupidTrunc K
        (embeddingUpIntGE (-((m : ℤ) - b)))
      naturality := fun m m' f => by
        have hmm : m ≤ m' := leOfHom f
        exact (StacksDraft.StupidTruncation.stupidTruncGEMapLE_ι K
          (show -((m' : ℤ) - b) ≤ -((m : ℤ) - b) by omega)).trans
          (Category.comp_id _).symm }

/-- **A complex is the colimit of its stupid truncations from below.**  In each degree `n` the
tower `σ^{≥ b - m}K` vanishes for `b - m > n` and the inclusion into `K` is an isomorphism as
soon as `b - m ≤ n`, so `isColimit_of_eventually_isIso` applies degreewise. -/
noncomputable def isColimit_truncCocone (K : CochainComplex B ℤ) (b : ℤ) :
    IsColimit (truncCocone K b) := by
  refine HomologicalComplex.isColimitOfEval _ _ (fun n => ?_)
  refine isColimit_of_eventually_isIso _ (b - n).toNat (fun m hm => ?_) (fun m hm => ?_)
  · change IsIso ((HomologicalComplex.ιStupidTrunc K
      (embeddingUpIntGE (-((m : ℤ) - b)))).f n)
    rw [StacksDraft.StupidTruncation.ιStupidTruncGE_f K _ n (by omega)]
    infer_instance
  · exact CochainComplex.isZero_of_isStrictlyGE
      (K.stupidTrunc (embeddingUpIntGE (-((m : ℤ) - b)))) (-((m : ℤ) - b)) n (by omega)

omit [HasColimitsOfShape ℕ B] [HasColimitsOfShape ℕ D]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)] in
/-- Each term of `truncDiagram K b` is K-flat, for `K` strictly bounded above by `b`: the term
at `m` is strictly bounded above by `b` and strictly bounded below by `b - m`, and in each
retained degree its term is the corresponding term of `K`. -/
lemma kFlat_truncDiagram_obj (K : CochainComplex B ℤ) (b : ℤ) [K.IsStrictlyLE b]
    (hterm : ∀ q : ℤ, KFlat F ((single B (ComplexShape.up ℤ) q).obj (K.X q))) (m : ℕ) :
    KFlat F ((truncDiagram K b).obj m) := by
  have h₁ : CochainComplex.IsStrictlyLE (K.stupidTrunc (embeddingUpIntGE (-((m : ℤ) - b)))) b :=
    inferInstance
  have h₂ : CochainComplex.IsStrictlyGE
      (K.stupidTrunc (embeddingUpIntGE (-((m : ℤ) - b)))) (-((m : ℤ) - b)) := inferInstance
  refine kFlat_of_bounds F m (K.stupidTrunc (embeddingUpIntGE (-((m : ℤ) - b))))
    (-((m : ℤ) - b)) b h₁ h₂ (by omega) (fun q hq _ => ?_)
  exact (hterm q).of_iso F ((single B (ComplexShape.up ℤ) q).mapIso
    (StacksDraft.StupidTruncation.stupidTruncGEXIso K (-((m : ℤ) - b)) q hq).symm)

omit [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
    (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
    K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)] in
/-- **Stacks Tag 06YQ, the engine completed: a complex which is strictly bounded above is
K-flat as soon as each of its terms, placed in its own degree, is.**

The source reduces the acyclic factor to a bounded above complex and invokes the first spectral
sequence of a double complex (Homology, Lemma 0132).  The route here filters the K-flat factor
from below instead: `K` is the colimit of its stupid truncations `σ^{≥ b - m}K`
(`isColimit_truncCocone`), each of which is bounded on both sides and therefore K-flat by
`kFlat_of_isStrictlyLE_of_isStrictlyGE`; and K-flatness passes to a colimit by
`kFlat_of_isColimit`.  That needs only that `Tot(F(G, -))` commutes with the colimit and that
the colimit is exact in `D`, the two hypotheses `hF` and `hexact`, both of which hold for
`F = ⊗_O` on a ringed site. -/
theorem kFlat_of_isStrictlyLE (K : CochainComplex B ℤ) (b : ℤ) [K.IsStrictlyLE b]
    (hF : ∀ X : A, PreservesColimitsOfShape ℕ (F.obj X))
    (hexact : ∀ (E : ℕ ⥤ CochainComplex D ℤ) (s : Cocone E), IsColimit s →
      (∀ i, (E.obj i).Acyclic) → s.pt.Acyclic)
    (hterm : ∀ q : ℤ, KFlat F ((single B (ComplexShape.up ℤ) q).obj (K.X q))) :
    KFlat F K :=
  kFlat_of_isColimit F (truncCocone K b) (isColimit_truncCocone K b) hF hexact
    (kFlat_truncDiagram_obj F K b hterm)

end BoundedAbove

end CochainComplex.KFlatBifunctor

end
