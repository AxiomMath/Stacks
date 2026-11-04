module

public import Mathlib.Algebra.Category.Grp.AB
public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.UpperBounds
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorTriangleShortExact
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Rlim

/-!
# A derived limit of a Mittag-Leffler tower of abelian groups keeps its upper bound

Let `(Kₙ)` be an inverse system in `D(Ab)` indexed by `ℕ` and let `K` be a derived limit of it,
presented as usual by a distinguished triangle `K ⟶ ∏ₙ Kₙ ⟶ ∏ₙ Kₙ ⟶ K⟦1⟧` whose middle map is
the Milnor difference `1 - shift`.  Suppose every `Kₙ` lies in degrees `≤ d`.  Then `K` lies in
degrees `≤ d + 1`, which is `Stacks.SmallDerivedCategory.isLE_of_isDerivedLimit`; the extra
degree comes from the shift in the defining triangle and is genuinely there in general, because
`H^{d+1}(K)` receives the first derived inverse limit `R¹ lim H^d(Kₙ)`.  The extra degree
disappears under the Mittag-Leffler condition on the cohomology systems `n ↦ H^i(Kₙ)`, which is
exactly what makes that `R¹ lim` vanish.

## Main results

* `Stacks.DerivedLimit.isMittagLeffler_of_eventually_surjective`: a tower of types whose
  successive transition maps are surjective from some stage on is Mittag-Leffler.
* `Stacks.DerivedLimit.epi_delta_of_isMittagLeffler`: the Milnor difference map of a
  Mittag-Leffler inverse system of abelian groups is an epimorphism.
* `Stacks.DerivedLimit.isLE_of_isDerivedLimit_of_isMittagLeffler`: a derived limit of a tower in
  `D(Ab)` lying in degrees `≤ d` with Mittag-Leffler cohomology systems lies in degrees `≤ d`.

## Implementation notes

The coefficient universe is free.  The two ingredients are the Milnor short exact sequence
`0 ⟶ R¹ lim H^{i-1}(Kₙ) ⟶ H^i(K) ⟶ lim H^i(Kₙ) ⟶ 0` of Tag 07KY at a given derived-limit
triangle, `DerivedCategory.exists_milnor_shortExact_of_distTriang`, which already presents
`R¹ lim` as the cokernel of the Milnor difference map on `∏ₙ H^{i-1}(Kₙ)` — this is where the
identification `H^{i-1}(∏ₙ Kₙ) ≅ ∏ₙ H^{i-1}(Kₙ)` of Tag 07KC part (3) is consumed, countable
products of abelian groups being exact — and the vanishing of that cokernel on a Mittag-Leffler
system, which is the Mittag-Leffler clause of `Rlim.lim_hasRightDerivedFunctor_and_computations`
(Tag 07KW) read through its cokernel clause.  Above `d` the inverse limit `lim H^i(Kₙ)` vanishes
term by term, so both outer terms of the sequence are zero.

`Rlim.delta` is the Milnor difference map of an inverse system of abelian groups; the difference
map occurring in the Milnor sequence is identified with it by `Rlim.delta_eq_lift`.

The Mittag-Leffler condition is Mathlib's `CategoryTheory.Functor.IsMittagLeffler` on the
underlying system of sets.

## References

* [Stacks Project, Tag 07KW](https://stacks.math.columbia.edu/tag/07KW)
* [Stacks Project, Tag 07KY](https://stacks.math.columbia.edu/tag/07KY)
* [Stacks Project, Tag 07KC](https://stacks.math.columbia.edu/tag/07KC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w m

namespace Stacks.DerivedLimit

attribute [local instance] HasDerivedCategory.standard

/-- The transition map of a tower of types over a composite of two inequalities factors. -/
private theorem map_homOfLE_op_eq_comp (X : ℕᵒᵖ ⥤ Type w) {a b c : ℕ} (h₁ : a ≤ b) (h₂ : b ≤ c)
    (h : a ≤ c) : X.map (homOfLE h).op = X.map (homOfLE h₂).op ≫ X.map (homOfLE h₁).op := by
  rw [← X.map_comp]
  exact congrArg X.map (Subsingleton.elim _ _)

/-- Every composite transition map of a tower of types, between two stages above one past which
the successive transition maps are surjective, is surjective. -/
private theorem surjective_map_of_eventually_surjective {X : ℕᵒᵖ ⥤ Type w} (n₀ : ℕ)
    (hs : ∀ n : ℕ, n₀ ≤ n → Function.Surjective (X.map (homOfLE (Nat.le_succ n)).op))
    (a b : ℕ) (ha : n₀ ≤ a) (hab : a ≤ b) :
    Function.Surjective (X.map (homOfLE hab).op) := by
  induction b, hab using Nat.le_induction with
  | base =>
      have h : (homOfLE (le_refl a)).op = 𝟙 (Opposite.op a) := Subsingleton.elim _ _
      rw [h, X.map_id]
      exact Function.surjective_id
  | succ b hab ih =>
      rw [map_homOfLE_op_eq_comp X hab (Nat.le_succ b)]
      exact ih.comp (hs b (ha.trans hab))

/-- **A tower of types whose successive transition maps are surjective from some stage on is
Mittag-Leffler.** The eventual range at a stage `j` is attained at `max j n₀`: a stage below that
one factors the transition from it, and a stage above it has surjective transition down to it. -/
public theorem isMittagLeffler_of_eventually_surjective {X : ℕᵒᵖ ⥤ Type w} (n₀ : ℕ)
    (hs : ∀ n : ℕ, n₀ ≤ n → Function.Surjective (X.map (homOfLE (Nat.le_succ n)).op)) :
    X.IsMittagLeffler := by
  intro j
  refine ⟨Opposite.op (max j.unop n₀), (homOfLE (le_max_left j.unop n₀)).op, ?_⟩
  intro k g
  have hjk : j.unop ≤ k.unop := leOfHom g.unop
  have hg : g = (homOfLE hjk).op := Subsingleton.elim _ _
  rcases le_total k.unop (max j.unop n₀) with hle | hle
  · rw [hg, map_homOfLE_op_eq_comp X hjk hle]
    rintro y ⟨x, rfl⟩
    exact ⟨X.map (homOfLE hle).op x, by simp⟩
  · rw [hg, map_homOfLE_op_eq_comp X (le_max_left j.unop n₀) hle hjk]
    rintro y ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := surjective_map_of_eventually_surjective n₀ hs
      (max j.unop n₀) k.unop (le_max_right j.unop n₀) hle x
    exact ⟨z, by simp [hz]⟩

/-- **The Milnor difference map of a Mittag-Leffler inverse system of abelian groups is an
epimorphism.** Its cokernel is the first derived inverse limit, which vanishes on a
Mittag-Leffler system; both facts are clauses of
`Rlim.lim_hasRightDerivedFunctor_and_computations`, Tag 07KW. -/
public theorem epi_delta_of_isMittagLeffler (A : Rlim.InvSystemAb.{m})
    (hA : (A ⋙ forget AddCommGrpCat.{m}).IsMittagLeffler) : Epi (Rlim.delta A) := by
  obtain ⟨RF, α, -, -, -, hML, -, -, -, hcoker, -⟩ :=
    Rlim.lim_hasRightDerivedFunctor_and_computations.{m}
  obtain ⟨e⟩ := hcoker A
  exact (Preadditive.epi_iff_isZero_cokernel _).2 (e.isZero_iff.1 (hML A hA))

/-- **A derived limit of a tower of `D(Ab)` with a uniform upper bound and Mittag-Leffler
cohomology systems keeps that upper bound.** Let `K` be a derived limit of `(Kₙ)`, presented by
its distinguished triangle `K ⟶ ∏ₙ Kₙ ⟶ ∏ₙ Kₙ ⟶ K⟦1⟧`, let every `Kₙ` lie in degrees `≤ d`, and
let each cohomology system `n ↦ H^i(Kₙ)` be Mittag-Leffler.  Then `K` lies in degrees `≤ d`.

This sharpens `Stacks.SmallDerivedCategory.isLE_of_isDerivedLimit`, which gives `d + 1` with no
Mittag-Leffler hypothesis.  In degree `i > d` the Milnor short exact sequence
`0 ⟶ R¹ lim H^{i-1}(Kₙ) ⟶ H^i(K) ⟶ lim H^i(Kₙ) ⟶ 0` has both outer terms zero: the right one
because every `H^i(Kₙ)` vanishes, and the left one — the cokernel of the Milnor difference map on
`∏ₙ H^{i-1}(Kₙ)` — because the degree-`(i-1)` system is Mittag-Leffler. -/
public theorem isLE_of_isDerivedLimit_of_isMittagLeffler
    (E : ℕᵒᵖ ⥤ DerivedCategory AddCommGrpCat.{m}) [HasProduct fun n : ℕ ↦ E.obj ⟨n⟩]
    (L : DerivedCategory AddCommGrpCat.{m}) (hL : IsDerivedLimit E L) (d : ℤ)
    (hE : ∀ n : ℕ, (E.obj ⟨n⟩).IsLE d)
    (hML : ∀ i : ℤ, ((E ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{m} i) ⋙
      forget AddCommGrpCat.{m}).IsMittagLeffler) :
    L.IsLE d := by
  obtain ⟨a, b, hT⟩ := hL
  rw [DerivedCategory.isLE_iff]
  intro i hi
  have hmil := DerivedCategory.exists_milnor_shortExact_of_distTriang E L a b hT i
  dsimp only at hmil
  obtain ⟨e, inc, prj, w, -, -, -, hSE⟩ := hmil
  have hcok : IsZero (cokernel (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ (E ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{m}
        (i - 1)).obj (Opposite.op n)) n -
      Pi.π (fun n : ℕ ↦ (E ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{m}
        (i - 1)).obj (Opposite.op n)) (n + 1) ≫
        (E ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{m}
          (i - 1)).map (homOfLE (Nat.le_succ n)).op)) := by
    have hepi := epi_delta_of_isMittagLeffler
      (E ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{m} (i - 1)) (hML (i - 1))
    rw [Rlim.delta_eq_lift] at hepi
    exact (Preadditive.epi_iff_isZero_cokernel _).1 hepi
  have hlim : IsZero (limit (E ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{m} i)) := by
    rw [IsZero.iff_id_eq_zero]
    refine limit.hom_ext fun n ↦ ?_
    have := hE n.unop
    exact (DerivedCategory.isZero_of_isLE (E.obj ⟨n.unop⟩) d i hi).eq_of_tgt _ _
  have : Epi inc := hSE.exact.epi_f (hlim.eq_of_tgt prj 0)
  rw [IsZero.iff_id_eq_zero, ← cancel_epi inc, comp_zero, Category.comp_id]
  exact hcok.eq_of_src _ _

end Stacks.DerivedLimit

end
