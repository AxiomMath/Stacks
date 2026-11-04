module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Pullback
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroup
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.RankReduction

/-!
# The rank class of a Weil cohomology theory

A finite locally free `𝒪_X`-module `ℰ` has a locally constant rank, so `X` is the disjoint union
of the open and closed loci `X_r` on which that rank is `r`; the decomposition is finite because
`X` is quasi-compact, and condition (2) of Stacks Section 45.12 then turns the tuple
`(0, 1, …, n)` into an element

`r^A(ℰ) ∈ A^0(X)`.

This is the **rank class**, the degree-zero part of the Chern character of Tag 0FI9. This file
constructs it, with its defining property.

## Main definitions

* `Stacks.WeilCohomology.SourceChernSetup.rankClass`: **the rank class `r^A(ℰ)`**, extended by zero
  off the finite locally free modules, which is the convention the universal property of the
  Grothendieck ring, Tag 0FEM, asks of an assignment on modules.

## Main results

* `Stacks.WeilCohomology.SourceChernSetup.exists_rankClass`: **the rank class exists.** This is the
  surjectivity half of condition (2) applied to the rank loci of `ℰ`, in the functorial form
  `Stacks.WeilCohomology.SourceChernSetup.exists_pull_eq_constantRank`.
* `Stacks.WeilCohomology.SourceChernSetup.rankClass_pull_eq`: **its defining property**: wherever
  the module acquires constant rank `r`, the rank class restricts to `r`.
* `Stacks.WeilCohomology.SourceChernSetup.rankClass_eq`: on a module of constant rank `r` the rank
  class is `r`.
* `Stacks.WeilCohomology.SourceChernSetup.rankClass_mem_grade`: **it lies in `A^0(X)`.**
* `Stacks.WeilCohomology.SourceChernSetup.pull_rankClass`: **it is compatible with pullback.**

## Construction

The rank class is constructed by splitting `X` into the open and closed pieces where `ℰ` has
constant rank, using quasi-compactness to make the decomposition finite, and reading the tuple of
ranks through `A(X) = ∏ A(X_r)`. Its properties come from the clauses of
`Stacks.WeilCohomology.SourceChernSetup`:

* that the class exists is the surjectivity half of condition (2), applied to the decomposition of
  `Stacks.WeilCohomology.SourceChernSetup.exists_pull_eq_constantRank`, with the constant family
  `m ↦ (m : A(Z))` as the datum to patch — a natural number is compatible with pullback because
  `f^*` is a ring map;
* that it lies in `A^0(X)` is condition (2) read as a splitting of *graded* rings,
  `Stacks.WeilCohomology.SourceChernSetup.mem_grade_of_pull_constantRank`, together with the fact
  that a natural number lies in degree zero;
* that it is compatible with pullback along an *arbitrary* morphism of `𝒞` is the second sentence
  of clause (2), which `Stacks.WeilCohomology.ClopenSubobject.exists_factor` transcribes: a
  morphism along which `ℰ` acquires a constant rank factors through the piece of `𝒞` indexing the
  locus of that rank.

## Implementation notes

`rankClass_pull_eq` is one statement doing the work of two: taking `g` to be the identity gives
the value of the rank class on a module that already has constant rank
(`Stacks.WeilCohomology.SourceChernSetup.rankClass_eq`), and feeding it the pieces of
`Stacks.WeilCohomology.SourceChernSetup.exists_clopenRankPieces` gives compatibility with pullback
(`Stacks.WeilCohomology.SourceChernSetup.pull_rankClass`).

Both are stated for a module `ℰ` which is itself finite locally free, and not merely for one
whose pullback is. The weaker reading is not just unprovable but false: a module which is not
finite locally free has rank class `0` by convention, while its pullback to a smaller object can
be finite locally free of any rank, and then `f^*(0) = 0` is not that rank unless `A` of the
smaller object is the zero ring.

## References

* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
* [Stacks Project, Tag 0FI9](https://stacks.math.columbia.edu/tag/0FI9)
* [Stacks Project, Tag 0FEM](https://stacks.math.columbia.edu/tag/0FEM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v v₁ w

namespace Stacks.WeilCohomology

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}

/-- The rank of a module pulled back along a composite, read through the comparison of iterated
pullbacks. -/
theorem isFiniteLocallyFreeOfRank_pullback_comp {X Y Z : C} (g : X ⟶ Y) (f : Y ⟶ Z)
    (E : (S.obj Z).Modules) (r : ℕ)
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map g)).obj ((Scheme.Modules.pullback (S.map f)).obj E)) r) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map (g ≫ f))).obj E) r :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
    ((Scheme.Modules.pullbackComp (S.map g) (S.map f)).app E ≪≫
      (Scheme.Modules.pullbackCongr (S.map_comp g f).symm).app E) h

/-- Pulling back twice is pulling back along the composite. -/
private theorem pull_pull_apply (𝔄 : SourceChernSetup.{u, v, v₁, w} C S) {X Y Z : C}
    (g : X ⟶ Y) (f : Y ⟶ Z) (a : 𝔄.A Z) : 𝔄.pull g (𝔄.pull f a) = 𝔄.pull (g ≫ f) a := by
  rw [𝔄.pull_comp]
  rfl

/-- **The reduction of two finite locally free modules to constant rank at once**, by iterating
`Stacks.WeilCohomology.SourceChernSetup.exists_clopenRankPieces`: decompose `X` by the rank of `ℰ`,
then each piece by the rank of the restriction of `ℱ`. On a piece of the result both modules have
constant rank, the morphism to `X` is still flat, and a class of `A(X)` is still determined by its
restrictions.

This is the form in which the additivity and the multiplicativity of the Chern character are
reduced to constant ranks: both are statements about two modules, the third one in a short exact
sequence having the rank forced. -/
theorem SourceChernSetup.exists_clopenRankPieces_pair (𝔄 : SourceChernSetup.{u, v, v₁, w} C S)
    (X : C)
    (E F : (S.obj X).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F) :
    ∃ (ι : Type) (_ : Finite ι) (P : ι → C) (p : ∀ i, P i ⟶ X) (rE rF : ι → ℕ),
      (∀ i, Flat (S.map (p i))) ∧
      (∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pullback (S.map (p i))).obj E) (rE i)) ∧
      (∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pullback (S.map (p i))).obj F) (rF i)) ∧
        Function.Injective fun a : 𝔄.A X => fun i => 𝔄.pull (p i) a := by
  classical
  obtain ⟨ι₁, hι₁, P₁, p₁, r₁, hflat₁, hr₁, hinj₁⟩ := 𝔄.exists_clopenRankPieces X E hE
  have : Finite ι₁ := hι₁
  choose ι₂ hι₂ P₂ p₂ r₂ hflat₂ hr₂ hinj₂ using fun i : ι₁ =>
    𝔄.exists_clopenRankPieces (P₁ i) ((Scheme.Modules.pullback (S.map (p₁ i))).obj F)
      (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme (S.map (p₁ i)) F hF)
  have : ∀ i, Finite (ι₂ i) := hι₂
  refine ⟨Σ i, ι₂ i, inferInstance, fun j => P₂ j.1 j.2, fun j => p₂ j.1 j.2 ≫ p₁ j.1,
    fun j => r₁ j.1, fun j => r₂ j.1 j.2, fun j => ?_, fun j => ?_, fun j => ?_, ?_⟩
  · have := hflat₁ j.1
    have := hflat₂ j.1 j.2
    rw [S.map_comp]
    infer_instance
  · exact isFiniteLocallyFreeOfRank_pullback_comp (p₂ j.1 j.2) (p₁ j.1) E (r₁ j.1)
      (@AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ (S.map (p₂ j.1 j.2)) _ _
        (hr₁ j.1))
  · exact isFiniteLocallyFreeOfRank_pullback_comp (p₂ j.1 j.2) (p₁ j.1) F (r₂ j.1 j.2)
      (hr₂ j.1 j.2)
  · intro a b hab
    refine hinj₁ (funext fun i => hinj₂ i (funext fun j => ?_))
    simpa only [pull_pull_apply] using congrFun hab ⟨i, j⟩

namespace SourceChernSetup

variable (𝔄 : SourceChernSetup.{u, v, v₁, w} C S)

/-- **The rank class exists.** There is a class of `A(X)` which restricts to `r` along every
morphism of `𝒞` along which `ℰ` acquires constant rank `r`, and which is `0` when `ℰ` is not
finite locally free.

For a finite locally free `ℰ` this is the patching half of condition (2),
`Stacks.WeilCohomology.SourceChernSetup.exists_pull_eq_constantRank`, applied to the datum that
assigns the natural number `m` to a morphism making the rank `m`: that datum is compatible with
further pullback because `f^*` is a ring map and so preserves natural numbers. -/
theorem exists_rankClass (X : C) (E : (S.obj X).Modules) :
    ∃ a : 𝔄.A X,
      (∀ (_ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E) (Z : C)
          (g : Z ⟶ X) (m : ℕ),
          AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
            ((Scheme.Modules.pullback (S.map g)).obj E) m → 𝔄.pull g a = (m : 𝔄.A Z)) ∧
        (¬ Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E → a = 0) := by
  by_cases hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E
  · obtain ⟨a, ha⟩ := 𝔄.exists_pull_eq_constantRank X E hE (fun Z _ m _ => (m : 𝔄.A Z))
      fun _ _ _ h m _ _ => map_natCast (𝔄.pull h) m
    exact ⟨a, fun _ Z g m hm => ha Z g m hm, fun hnot =>
      absurd ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry E).mpr hE)
        hnot⟩
  · exact ⟨0, fun hE' => absurd hE' hE, fun _ => rfl⟩

/-- **The rank class `r^A(ℰ)`**, extended by zero off the finite locally free modules: the class
of `A^0(X)` which restricts to the constant rank of `ℰ` wherever `ℰ` acquires one. -/
def rankClass (X : C) (E : (S.obj X).Modules) : 𝔄.A X := (𝔄.exists_rankClass X E).choose

/-- **The defining property of the rank class**: wherever a finite locally free module acquires
constant rank `r`, its rank class restricts to `r`. -/
theorem rankClass_pull_eq {X Y : C} (g : X ⟶ Y) (E : (S.obj Y).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E) (r : ℕ)
    (hr : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map g)).obj E) r) :
    𝔄.pull g (𝔄.rankClass Y E) = (r : 𝔄.A X) :=
  (𝔄.exists_rankClass Y E).choose_spec.1 hE X g r hr

/-- The rank class vanishes off the finite locally free modules, which is the normalisation the
universal property of the Grothendieck ring asks for. -/
theorem rankClass_eq_zero (X : C) (M : (S.obj X).Modules)
    (h : ¬ Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M) : 𝔄.rankClass X M = 0 :=
  (𝔄.exists_rankClass X M).choose_spec.2 h

/-- **The rank class of a module of constant rank `r` is `r`.** This is the defining property at
the identity morphism. -/
theorem rankClass_eq (X : C) (M : (S.obj X).Modules) (r : ℕ)
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r) :
    𝔄.rankClass X M = (r : 𝔄.A X) := by
  have h' := 𝔄.rankClass_pull_eq (𝟙 X) M h.isFiniteLocallyFree r
    (@AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ (S.map (𝟙 X)) M r h)
  rwa [𝔄.pull_id X, RingHom.id_apply] at h'

/-- **The rank class lies in `A^0(X)`.** Its restriction to every piece on which the rank is
constant is a natural number, which lies in degree zero, and condition (2) is a splitting of
graded rings. -/
theorem rankClass_mem_grade (X : C) (M : (S.obj X).Modules) :
    𝔄.rankClass X M ∈ 𝔄.grade X 0 := by
  by_cases hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M
  · refine 𝔄.mem_grade_of_pull_constantRank X M hM _ 0 fun Z g _ m hm => ?_
    rw [𝔄.rankClass_pull_eq g M hM m hm]
    exact 𝔄.natCast_mem_grade_zero Z m
  · rw [𝔄.rankClass_eq_zero X M fun h =>
      hM ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry M).mp h)]
    exact (𝔄.grade X 0).zero_mem

/-- **The rank class is compatible with pullback.** Restricting to the pieces on which the
pulled-back module has constant rank, which is
`Stacks.WeilCohomology.SourceChernSetup.exists_clopenRankPieces`, both sides become that constant
rank, and a class is determined by those restrictions. -/
theorem pull_rankClass {X Y : C} (f : X ⟶ Y) (E : (S.obj Y).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E) :
    𝔄.pull f (𝔄.rankClass Y E) = 𝔄.rankClass X ((Scheme.Modules.pullback (S.map f)).obj E) := by
  have hE' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback (S.map f)).obj E) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme (S.map f) E hE
  obtain ⟨ι, -, P, p, r, -, hr, hinj⟩ :=
    𝔄.exists_clopenRankPieces X ((Scheme.Modules.pullback (S.map f)).obj E) hE'
  refine hinj (funext fun i => ?_)
  dsimp only
  rw [pull_pull_apply,
    𝔄.rankClass_pull_eq (p i ≫ f) E hE (r i)
      (isFiniteLocallyFreeOfRank_pullback_comp (p i) f E (r i) (hr i)),
    𝔄.rankClass_pull_eq (p i) _ hE' (r i) (hr i)]

end SourceChernSetup

end Stacks.WeilCohomology

end
